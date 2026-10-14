import Examples.BareMetalCounter

/-!
Reference frames for the bare-metal host test: the exported functions run
natively (full Lean runtime) on the same event script as `baremetal/host/main.c`.
`baremetal/tools/host_test.sh` checks that the C bundle (no `libleanrt`)
produces byte-identical RGB565 frames.
-/

open Examples.BareMetalCounter

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  IO.FS.createDirAll dir
  let s := init 320 240 64 16
  let s := beginFrame s
  IO.FS.writeBinFile s!"{dir}/frame0.rgb565" (frameRGB565 s)
  let s := event s 4 1 0
  let s := event s 4 1 0
  let s := event s 4 1 0
  let s := event s 4 2 0
  let s := event s 2 30 200
  let s := beginFrame s
  IO.FS.writeBinFile s!"{dir}/frame1.rgb565" (frameRGB565 s)
