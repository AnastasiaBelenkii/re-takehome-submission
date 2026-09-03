# Git-to-run evidence references

Each branch below contains one evidence commit whose direct parent is the exact
code commit recorded in the archived run provenance. The evidence commit holds
the associated raw transcript JSON, an original-path index, public artifact
pointers, and checksums. The remainder of the large raw archives stays in object
storage.

| Evidence branch | Generating parent | Provenance records | Unique transcripts |
|---|---|---:|---:|
| `evidence/run-data-16f65f6e963c` | `16f65f6e963cfe86a9776fe7cf1215e317e11681` | 9 | 3 |
| `evidence/run-data-203f42478717` | `203f42478717fd8f8c2dd65c6a521bc4e1c4f48c` | 4 | 24 |
| `evidence/run-data-2eca9293a0d4` | `2eca9293a0d4754cbc0615bdbe1d132436caf490` | 9 | 9 |
| `evidence/run-data-425a5c8b38fd` | `425a5c8b38fd8935911546dd6cd7e1ecee122a7b` | 3 | 1 |
| `evidence/run-data-5c1a990de114` | `5c1a990de11480b82914d91a54ce2b7f85d2216c` | 1 | 1 |
| `evidence/run-data-73eb36dbe07a` | `73eb36dbe07abfa23141ffbabce4c4d65d7567a8` | 149 | 94 |
| `evidence/run-data-88b5631180f6` | `88b5631180f66041bb04d88c530ae22ec97711fd` | 2 | 32 |
| `evidence/run-data-a7439fa6f02e` | `a7439fa6f02e838e16602b746f097960822b34de` | 3 | 3 |
| `evidence/run-data-a87f19ba8d4c` | `a87f19ba8d4c487e5d97e85b0e0d2e9d8afdd95b` | 7 | 112 |
| `evidence/run-data-cdaaac9524cb` | `cdaaac9524cbc924a6ab969ca23da21529a62c3c` | 1 | 1 |
| `evidence/run-data-d6640c7ba3a1` | `d6640c7ba3a184c9767077bb89b6c97e7ba935f2` | 3 | 3 |
| `evidence/run-data-e1c8fee0a5db` | `e1c8fee0a5dbe1b751cb7dfe8ac3ddf759c51462` | 54 | 27 |
| `evidence/run-data-e8af4fb7d278` | `e8af4fb7d278cbf7c5e3e636716a6512f85da140` | 56 | 56 |

Verify any relationship after fetching the branches:

```bash
branch=evidence/run-data-e8af4fb7d278
git rev-parse "$branch^"
git show "$branch:evidence/ARCHIVE_POINTER.json"
git show "$branch:evidence/TRANSCRIPT_INDEX.json"
```

The index covers 301 archived provenance records. Artifacts without an explicit
full `git_commit` are retained in the public dataset but are not assigned to a
parent commit by inference.

The separate `evidence/all-transcripts-20260902` convenience branch contains
all 485 unique raw transcript payloads and an index covering all 2,564 archived
paths. It is the simplest Git-only entry point, but it does not assert that its
own parent generated every transcript.

Browse it at
<https://github.com/AnastasiaBelenkii/re-takehome-submission/tree/evidence/all-transcripts-20260902/evidence>,
or fetch it without switching the working branch:

```bash
git fetch origin evidence/all-transcripts-20260902
git worktree add ../re-takehome-transcripts FETCH_HEAD
```

## Endpoint outcomes

The `evidence/results-20260902` branch is the Git-only endpoint evidence mirror.
It contains 5,499 original files:

| Filename | Archived paths | Unique Git blobs |
|---|---:|---:|
| `result.json` | 2,576 | 512 |
| `events.jsonl` | 2,564 | 498 |
| `provenance.json` | 301 | 221 |
| `preliminary-status.json` | 58 | 58 |

Browse it at
<https://github.com/AnastasiaBelenkii/re-takehome-submission/tree/evidence/results-20260902/evidence>,
or fetch it independently of the transcript branch:

```bash
git fetch origin evidence/results-20260902
git worktree add ../re-takehome-results FETCH_HEAD
```

Paths begin with either `evidence/archives/legacy-20260901/` or
`evidence/archives/matched-stage3-20260902/`. Duplicate mirrors retain their
original paths while Git deduplicates their identical blob contents.
