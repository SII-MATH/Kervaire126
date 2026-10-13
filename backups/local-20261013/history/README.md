# Local development archive — 2026-10-13

This archive belongs to `SII-MATH/Kervaire126`, branch
`codex/local-backup-20261013`. Its parent checkpoint is `db022afd9`.
It preserves the two other local repositories without merging their different
mathematical interfaces into Kervaire126's active source tree.

| Source working directory | Current branch | Changed tracked files | Untracked files | Local branches preserved |
| --- | --- | ---: | ---: | ---: |
| `/home/wang/KIP126` | `wang-dev` | 18 | 37 | 3 |
| `/home/wang/KIP-base` | `recovery/commutativity-proof-work` | 10 | 56 | 2 |

The archives include every changed/untracked path reported by Git at capture,
including duplicate source files, work notes, connector configuration,
Blueprint copies, and generated files. No files were discarded merely because
another remote already contained the same content.

## Layout

Each repository directory contains:

- `manifest.json`: original directory, remote, HEAD, all local branch/tag tips,
  remote-ref snapshot, original path/status, file SHA-256 values, artifact
  SHA-256 values, and verification results.
- `worktree-changes.tar.gz`: exact contents of every changed/untracked file,
  preserving original relative paths and executable modes.
- `tracked-changes.patch`: binary-capable tracked-file diff relative to HEAD.
- `staged-changes.patch`: the separately recorded index diff (empty at capture).
- `history.bundle` or ordered `history.bundle.part-NNN` files: self-contained
  Git history for every local branch and tag, including commits absent from the
  source repository's remote branches. KIP126's bundle is split into parts
  below the hosting service's single-file size limit.

In particular, KIP126's `codex/lambda-quotient-tower-proof` branch is preserved,
including its 13 commits absent from that repository's origin branch histories.

## Verify or restore

Requires Python 3.12+ and Git. Run from any directory:

```sh
python3 /absolute/path/to/this/archive/restore.py KIP126 --verify-only
python3 /absolute/path/to/this/archive/restore.py KIP-base --verify-only
python3 /absolute/path/to/this/archive/restore.py KIP126 --destination /new/empty/location/KIP126
python3 /absolute/path/to/this/archive/restore.py KIP-base --destination /new/empty/location/KIP-base
```

The destination must not already exist. Restoration reconstructs the Git
history, all local branches, current branch, index state, and changed/untracked
files, and checks the restored file hashes. It restores the original origin URL
but does not contact or push to that origin. It validates the resulting Git
status against the captured status before reporting success.

Both archives were actually restored into new temporary working directories
before this archive was committed. All 55 / 66 changed-file statuses, file
hashes, and all 3 / 2 local branch tips matched the source snapshots.

## Scope and proof status

Ignored dependency/build caches (`.lake`, compiled Lean output, etc.) are outside
the archive. External Git LFS payloads for unchanged historical inputs are not
embedded in Git bundles; their pointer files and source history are preserved.
No changed/untracked input in this capture is omitted on that basis.

These are recovery snapshots of development work. Archive integrity, successful
restoration, and successful Git checks do not certify the mathematical statements
or complete any unfinished proof. Existing `sorry`, source premises, and model
assumptions are preserved verbatim. No active Lean or Blueprint statement is
modified by adding this archive.
