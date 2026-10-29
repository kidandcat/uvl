# Security

## Supported versions

There are no GitHub releases yet. `0.1.0` is the version declared on `main`
([CHANGELOG.md](CHANGELOG.md)); it is not a support commitment. Fixes go to
`main`. When a `vX.Y.Z` tag exists, only the latest release gets security
fixes unless a notice says otherwise.

## Reporting

Please report a vulnerability through a private GitHub security advisory:

https://github.com/kidandcat/uvl/security/advisories/new

Do not open a public issue, pull request, or discussion for an unfixed
vulnerability, and do not include a proof of concept in a public place.

Include what you ran, the Lean toolchain (`lean-toolchain`), the host
(desktop, browser, Android, bare metal), and the effect you observed.
Build scripts download Lean, wgpu-native, libuv, SDL, and Emscripten. A
problem in that supply chain is in scope for this process too.

We will acknowledge the report, confirm or reject it, and agree on a fix
before any public description.
