#!/usr/bin/env python3
"""
uvl_bundle.py: turn the C that Lean generated for a UVL app into a
self-contained, libleanrt-free source bundle for a microcontroller.

    uvl_bundle.py --lean-prefix $(lean --print-prefix) \
                  --ir .lake/build/ir --init-c .lake/baremetal/init-c \
                  --out .lake/baremetal/bundle

What it does

1. Takes every generated C file of the package (`--ir`) and of Lean's `Init`
   library (`--init-c`, regenerated from the toolchain's sources by
   `gen_init_c.sh`, since the toolchain only ships them compiled for the host).
2. Replaces each module initializer: instead of initializing *every* top-level
   constant of the module and recursively every imported module (all of
   `Init`, i.e. thousands of objects), it gets a `uvl_modinit_<module>()` that
   initializes only the constants the app can actually reach.
3. Finds that reachable set with the host linker: link with --gc-sections from
   the exported `uvl_*` entry points, read which constant sections survived,
   regenerate the initializers, repeat until nothing changes.
4. Writes the files that still contribute code, a `uvl_init.c` calling the
   module initializers in import order, the runtime (`rt/`), the headers
   (`include/` + the toolchain's `lean.h`) and `uvl_bundle.cmake`.

Closed terms (`_closed_N`) need no handling: Lean emits them as `static const`
objects (flash) or lazily initialized once-cells.
"""
import argparse
import concurrent.futures
import hashlib
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
BAREMETAL = os.path.dirname(HERE)

INIT_FN = re.compile(
    r'(?:lean_object\* (?:runtime_|meta_)?initialize_\w+\(uint8_t builtin\);\n)*'
    r'(?:void lean_initialize(?:_runtime_module)?\(\);\n)?'
    r'static bool _G_(?:runtime_|meta_)?initialized = false;\n'
    r'LEAN_EXPORT lean_object\* (?:runtime_|meta_)?initialize_\w+\(uint8_t builtin\) \{\n(.*?)\n\}\n',
    re.S)
ASSIGN = re.compile(r'^(\w+) = _init_(\w+)\(\);$')
PERSIST = re.compile(r'^lean_mark_persistent\((\w+)\);$')
IO_CALL = re.compile(r'^res = (\w+)\(\);$')
IO_GET = re.compile(r'^(\w+) = lean_io_result_get_value\(res\);$')
SKIP = re.compile(
    r'^(lean_object \* res;|res = \w+\(builtin\);|if \(lean_io_result_is_error\(res\)\) return res;|'
    r'lean_dec_ref\(res\);|return lean_io_result_mk_ok\(lean_box\(0\)\);|'
    r'if \(_G_\w*initialized\) return lean_io_result_mk_ok\(lean_box\(0\)\);|_G_\w*initialized = true;|'
    r'lean_initialize(_runtime_module)?\(\);|return \w*initialize_\w+\(builtin\);)$')
IMPORTS = re.compile(r'^// Imports:(.*)$', re.M)
MODULE = re.compile(r'^// Module: (\S+)$', re.M)


def fix_literals(text):
    """The compiler decides at compile time, for a 64-bit target, that a Nat
    literal below 2^63 is an unboxed scalar and never needs a `lean_dec`. On a
    32-bit MCU literals of 2^31 and above are heap objects, so each evaluation
    would leak one. Route them to `uvl_nat_literal`, which returns interned,
    persistent objects (rt/uvl_rt.c)."""
    text = text.replace('lean_cstr_to_nat(', 'uvl_nat_literal(').replace('lean_cstr_to_int(', 'uvl_int_literal(')
    text = re.sub(r'lean_unsigned_to_nat\((\d+)u\)',
                  lambda m: m.group(0) if int(m.group(1)) < 2**31 else f'uvl_nat_literal("{m.group(1)}")', text)
    if 'uvl_nat_literal(' in text or 'uvl_int_literal(' in text:
        text = text.replace('#include <lean/lean.h>\n', '#include <lean/lean.h>\n'
                            'LEAN_EXPORT lean_object *uvl_nat_literal(char const *s);\n'
                            'LEAN_EXPORT lean_object *uvl_int_literal(char const *s);\n', 1)
    return text


def cident(module):
    return re.sub(r'[^A-Za-z0-9_]', '_', module)


class Unit:
    """One generated C file."""

    def __init__(self, path):
        self.path = path
        self.src = open(path).read()
        m = MODULE.search(self.src)
        self.module = m.group(1) if m else os.path.basename(path)[:-2]
        m = IMPORTS.search(self.src)
        self.imports = [w for w in (m.group(1).split() if m else []) if w not in ('import', 'public', 'meta', 'all')]
        self.consts = []          # [(name, [statements])] in initialization order
        self.unknown = []
        parts = []
        last = 0
        for m in INIT_FN.finditer(self.src):
            parts.append(self.src[last:m.start()])
            last = m.end()
            lines = [l.strip() for l in m.group(1).split('\n') if l.strip()]
            pending = None   # `res = <initFn>();` of an `initialize` declaration
            for line in lines:
                a = ASSIGN.match(line)
                p = PERSIST.match(line)
                io = IO_CALL.match(line)
                g = IO_GET.match(line)
                if a:
                    self.consts.append((a.group(1), [line]))
                elif io:
                    pending = line
                elif g and pending:
                    self.consts.append((g.group(1), [pending, line]))
                    pending = None
                elif p and self.consts and self.consts[-1][0] == p.group(1):
                    self.consts[-1][1].append(line)
                elif line == 'lean_dec_ref(res);' and self.consts and self.consts[-1][1][0].startswith('res = '):
                    self.consts[-1][1].append(line)
                elif not SKIP.match(line):
                    self.unknown.append(line)
        parts.append(self.src[last:])
        self.body = fix_literals(''.join(parts))
        if not INIT_FN.search(self.src):
            raise SystemExit(f'{path}: no module initializer found')

    @property
    def fn(self):
        return 'uvl_modinit_' + cident(self.module)

    def render(self, keep):
        stmts = [s for name, ss in self.consts if name in keep for s in ss]
        init = 'void %s(void) {\n    lean_object * res;\n%s}\n' % (
            self.fn, ''.join('    %s\n' % s for s in stmts))
        tail = self.body.rfind('#ifdef __cplusplus\n}')
        if tail < 0:
            tail = len(self.body)
        return self.body[:tail] + init + self.body[tail:], bool(stmts)


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if r.returncode != 0:
        sys.stderr.write(' '.join(cmd[:8]) + ' ...\n' + r.stdout + r.stderr)
        raise SystemExit(r.returncode)
    return r


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--lean-prefix', required=True)
    ap.add_argument('--ir', required=True, help='lake IR directory (.lake/build/ir)')
    ap.add_argument('--init-c', required=True, help='C regenerated for Init (gen_init_c.sh)')
    ap.add_argument('--extra-c', help='where to generate C for Std/Lean modules the app turns out to need '
                    '(default: <init-c>/../extra-c)')
    ap.add_argument('--out', required=True)
    ap.add_argument('--work', help='scratch directory (default: <out>.work)')
    ap.add_argument('--cc', default='cc')
    ap.add_argument('--host-heap-kb', type=int, default=256, help='pool size of the host harness')
    ap.add_argument('--entry', default='Examples.BareMetalCounter',
                    help='module that exports the uvl_* functions; only its imports are bundled')
    args = ap.parse_args()

    work = args.work or args.out.rstrip('/') + '.work'
    os.makedirs(os.path.join(work, 'src'), exist_ok=True)
    os.makedirs(os.path.join(work, 'obj'), exist_ok=True)
    lean_inc = os.path.join(args.lean_prefix, 'include')
    incs = ['-I', os.path.join(BAREMETAL, 'include'), '-I', lean_inc]
    cflags = ['-O1', '-w', '-ffunction-sections', '-fdata-sections', '-fno-common'] + incs
    host_heap = ['-DUVL_HEAP_SIZE=%d' % (args.host_heap_kb * 1024)]

    files = []
    for root, _, names in os.walk(args.ir):
        for n in names:
            if n.endswith('.c'):
                files.append(os.path.join(root, n))
    files += [os.path.join(args.init_c, n) for n in os.listdir(args.init_c) if n.endswith('.c')]
    units = {}

    def load(f):
        u = Unit(f)
        if u.unknown:
            print(f'warning: {u.module}: unhandled initializer statements {u.unknown[:3]}', file=sys.stderr)
        units[u.module] = u
    extra = args.extra_c or os.path.join(os.path.dirname(os.path.abspath(args.init_c)), 'extra-c')
    if os.path.isdir(extra):
        files += [os.path.join(extra, n) for n in os.listdir(extra) if n.endswith('.c')]
    for f in sorted(files):
        load(f)
    # keep only the package modules the entry module imports (others may define `main`)
    package = {m for m, u in units.items() if os.path.abspath(u.path).startswith(os.path.abspath(args.ir))}
    needed, todo = set(), [args.entry]
    while todo:
        m = todo.pop()
        if m in needed or m not in units:
            continue
        needed.add(m)
        todo += units[m].imports
    if args.entry not in units:
        raise SystemExit(f'entry module {args.entry} not found under {args.ir}')
    for m in package - needed:
        del units[m]
    print(f'{len(units)} modules')

    def compile_unit(u, keep):
        text, _ = u.render(keep)
        c = os.path.join(work, 'src', cident(u.module) + '.c')
        o = os.path.join(work, 'obj', cident(u.module) + '.o')
        digest = hashlib.sha1((text + ' '.join(cflags)).encode()).hexdigest()
        stamp = o + '.sha1'
        if os.path.exists(stamp) and open(stamp).read() == digest:
            return
        with open(c, 'w') as fh:
            fh.write(text)
        run([args.cc] + cflags + ['-c', c, '-o', o])
        with open(stamp, 'w') as fh:
            fh.write(digest)

    def module_order():
        order, seen = [], set()

        def visit(m):
            if m in seen or m not in units:
                return
            seen.add(m)
            for i in units[m].imports:
                visit(i)
            order.append(m)
        for m in sorted(units):
            visit(m)
        return order

    symbol_index = {}

    def defining_modules(sym):
        """Toolchain modules (Init/Std/Lean) whose object code defines `sym`."""
        if not symbol_index:
            for lib in ('libInit.a', 'libStd.a', 'libLean.a'):
                r = run(['nm', '-A', '--defined-only', os.path.join(args.lean_prefix, 'lib', 'lean', lib)])
                for line in r.stdout.splitlines():
                    parts = line.split()
                    if len(parts) == 3 and parts[1] in 'TDBRtdbr':
                        member = parts[0].rsplit(':', 2)[-2].split('.')[0]
                        symbol_index.setdefault(parts[2], set()).add(member)
        out = []
        src = os.path.join(args.lean_prefix, 'src', 'lean')
        for stem in symbol_index.get(sym, ()):
            cands = []
            for top in ('Init', 'Std', 'Lean'):
                for root, _, names in os.walk(os.path.join(src, top)):
                    if stem + '.lean' in names:
                        cands.append(os.path.relpath(os.path.join(root, stem + '.lean'), src))
            hit = [c for c in cands if c[:-5].replace('/', '_') in sym]
            out += hit or cands
        return out
    rt = [os.path.join(BAREMETAL, 'rt', f) for f in ('uvl_rt.c', 'uvl_shell.c')]
    harness = os.path.join(BAREMETAL, 'host', 'main.c')
    keep = set()
    it = 0
    while True:
        it += 1
        order = module_order()
        with concurrent.futures.ThreadPoolExecutor(os.cpu_count()) as ex:
            list(ex.map(lambda u: compile_unit(u, keep), units.values()))
        init_c = os.path.join(work, 'uvl_init.c')
        with open(init_c, 'w') as fh:
            fh.write('/* Generated by uvl_bundle.py: initialize only what the app reaches. */\n')
            calls = [units[m].fn for m in order if units[m].render(keep)[1]]
            fh.write(''.join(f'void {c}(void);\n' for c in calls))
            fh.write('void uvl_rt_init(void) {\n' + ''.join(f'    {c}();\n' for c in calls) + '}\n')
        exe = os.path.join(work, 'uvl-host')
        mapf = os.path.join(work, 'link.map')
        objs = [os.path.join(work, 'obj', cident(m) + '.o') for m in order]
        r = subprocess.run([args.cc] + cflags + host_heap + [harness, init_c] + rt + objs +
                           ['-o', exe, '-lm', '-Wl,--gc-sections', '-Wl,--print-gc-sections', f'-Wl,-Map={mapf}'],
                           capture_output=True, text=True)
        if r.returncode != 0:
            missing = sorted(set(re.findall(r"undefined reference to `(\w+)'", r.stderr)))
            if not missing:
                sys.stderr.write(r.stderr)
                raise SystemExit(1)
            runtime = [m for m in missing if m.startswith('lean_')]
            if runtime:
                raise SystemExit('runtime functions missing from rt/uvl_rt.c: ' + ', '.join(runtime))
            mods = sorted({f for m in missing for f in defining_modules(m)})
            if not mods:
                raise SystemExit('cannot find the module defining: ' + ', '.join(missing))
            print(f'iteration {it}: {len(missing)} symbols live in {mods}; generating their C')
            run([os.path.join(HERE, 'gen_c.sh'), args.lean_prefix, extra] + mods)
            for f in mods:
                load(os.path.join(extra, f[:-5].replace('/', '.') + '.c'))
            continue
        removed = set()
        for line in r.stderr.splitlines():
            m = re.search(r"removing unused section '\.(?:bss|data)\.(\w+)' in file", line)
            if m:
                removed.add(m.group(1))
        new_keep = {name for u in units.values() for name, _ in u.consts if name not in removed}
        print(f'iteration {it}: {len(new_keep)} constants reachable')
        if new_keep == keep:
            break
        keep = new_keep

    # bundle: the units whose code survived garbage collection
    mapped = open(mapf).read().split('Linker script and memory map', 1)[1]
    alive = set()
    for m in re.finditer(r'^ \.(?:text|rodata|data|bss)\S*\s*\n?\s+0x[0-9a-f]+\s+0x([0-9a-f]+)\s+\S+?/obj/(\w+)\.o$',
                         mapped, re.M):
        if int(m.group(1), 16) > 0:
            alive.add(m.group(2))
    used = [m for m in order if cident(m) in alive]
    out = args.out
    if os.path.isdir(out):
        shutil.rmtree(out)
    os.makedirs(os.path.join(out, 'src'))
    for m in used:
        shutil.copy(os.path.join(work, 'src', cident(m) + '.c'), os.path.join(out, 'src'))
    shutil.copy(os.path.join(work, 'uvl_init.c'), os.path.join(out, 'src'))
    shutil.copytree(os.path.join(BAREMETAL, 'rt'), os.path.join(out, 'rt'))
    shutil.copytree(os.path.join(BAREMETAL, 'include'), os.path.join(out, 'include'))
    for h in ('lean.h', 'version.h'):
        shutil.copy(os.path.join(lean_inc, 'lean', h), os.path.join(out, 'include', 'lean'))
    srcs = sorted(os.listdir(os.path.join(out, 'src')))
    with open(os.path.join(out, 'uvl_bundle.cmake'), 'w') as fh:
        fh.write('# Generated by uvl_bundle.py\n')
        fh.write('set(UVL_BUNDLE_DIR ${CMAKE_CURRENT_LIST_DIR})\n')
        fh.write('set(UVL_BUNDLE_SOURCES\n' +
                 ''.join(f'  ${{UVL_BUNDLE_DIR}}/src/{s}\n' for s in srcs) +
                 '  ${UVL_BUNDLE_DIR}/rt/uvl_rt.c\n  ${UVL_BUNDLE_DIR}/rt/uvl_shell.c)\n')
        fh.write('set(UVL_BUNDLE_INCLUDE ${UVL_BUNDLE_DIR}/include)\n')
    shutil.copy(exe, os.path.join(out, 'uvl-host'))
    print(f'bundle: {len(used)} of {len(units)} modules, {len(keep)} constants -> {out}')


if __name__ == '__main__':
    main()
