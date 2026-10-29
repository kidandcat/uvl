# Releasing

UVL uses [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

The version lives in one place in code: the `package uvl` block of
`lakefile.lean`,

```lean
version := v!"X.Y.Z"
```

and it must equal the newest numbered heading in [CHANGELOG.md](CHANGELOG.md)
(`## [X.Y.Z] - YYYY-MM-DD`). `scripts/check-version.sh` checks that. CI runs
the script on every pull request and on every push to `main`.

Versions `0.x.y` are development versions. A breaking source change may ship
as a minor bump. `1.0.0`, when it exists, is the first version that follows
the usual major / minor / patch intent as closely as a Lean package can.

## Steps

1. Choose `X.Y.Z`. The Lake literal has no leading `v`. The git tag does.
2. Move the notes under `## [Unreleased]` in `CHANGELOG.md` into a new section
   `## [X.Y.Z] - YYYY-MM-DD`. Leave an empty `## [Unreleased]` section above
   it. Follow [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
3. Set `version := v!"X.Y.Z"` in `lakefile.lean`.
4. Run `scripts/check-version.sh` and `lake build` on a clean tree.
5. Commit those files on `main` (via a pull request).
6. Tag that commit and push the tag:

   ```sh
   git tag -a vX.Y.Z -m "vX.Y.Z"
   git push origin vX.Y.Z
   ```

7. Publish a GitHub release for `vX.Y.Z`. Use the new changelog section as the
   release notes.

Tag only the commit that already contains the matching version and changelog.
Do not move a tag that has been published. Do not create a release from an
unreleased heading.
