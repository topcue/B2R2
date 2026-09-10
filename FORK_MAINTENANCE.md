# Personal Fork Maintenance

This repository is the `topcue/B2R2` research fork of the official
`B2R2-org/B2R2` repository. This document records the maintenance agreement for
future workers so that the policy does not depend on conversation history.

## Repository Roles

- `origin` is `https://github.com/topcue/B2R2.git`. Publish fork changes only to
  this repository.
- `upstream` is `https://github.com/B2R2-org/B2R2.git`. It is read-only. Never
  push to it or open a pull request against it for this research work.
- Keep the upstream push URL disabled in local clones when possible:
  `disabled://B2R2-org/B2R2`.

## Fork-Owned Diff Boundary

The enhanced binary diff is fork-owned research functionality. Keep its
implementation under:

```text
src/RearEnd/Transformer/ForkDiff/
```

The public action IDs have distinct purposes:

- `diff` selects `ForkDiff.EnhancedDiffAction`.
- `legacy-diff` preserves the official B2R2 `DiffAction` for comparison and
  compatibility.

Do not move the enhanced implementation back into the official
`Transformer/DiffAction.fs` or `Transformer/Program.fs`. Keep changes to
upstream-owned files limited to small registration or dispatch points. The
expected integration points are:

- `src/RearEnd/Transformer/B2R2.RearEnd.Transformer.fsproj`: compile the
  fork-owned files.
- `src/RearEnd/Transformer/DiffAction.fs`: reserve `legacy-diff` for the
  official implementation.
- `src/RearEnd/Launcher/Program.fs`: dispatch the top-level `diff` command.

Tests for the fork-owned diff live in `src/RearEnd/Transformer.Tests`. They must
verify both the enhanced behavior and the distinct action IDs.

## Updating From Official B2R2

Perform each official update as an explicit, reviewable operation:

1. Confirm the B2R2 worktree is clean and `main` matches `origin/main`.
2. Fetch both `origin` and `upstream` with pruning enabled.
3. Review the upstream commits and changed files before integrating them.
4. Integrate `upstream/main` on a temporary fork-owned update branch. Do not
   publish anything to upstream.
5. Preserve upstream behavior in upstream-owned files. Reapply only the small
   integration points listed above; keep substantive diff code in `ForkDiff`.
6. Review `git diff upstream/main...HEAD`, paying particular attention to any
   new upstream changes in the integration-point files.
7. Run the complete verification sequence from `AGENTS.md`.
8. Smoke-test `diff`, `legacy-diff`, and at least one real executable section.
9. Merge the verified update into the fork's `main` and push only to `origin`.

Prefer a normal merge of official updates into the published fork branch so
existing commit IDs remain stable. Do not rewrite a commit already pinned by a
research project unless the user explicitly authorizes it.

## Required Verification

Run these commands separately from the repository root:

```text
dotnet build
dotnet fslint src --strict
dotnet test
```

The Windows checkout may report pre-existing CRLF lint failures in unchanged
upstream files. Do not silently treat new warnings as part of that baseline.
Confirm that every file changed by the fork is LF, passes the applicable lint
rules, and passes `git diff --check`.

For the enhanced diff, also verify:

- byte, text, instruction, and section modes;
- Myers and Histogram algorithms;
- side-by-side, summary, and JSON output;
- batch input and JSONL output;
- ISA and section selection;
- simultaneous registration of `diff` and `legacy-diff`.

## Research-Project Submodule

The `ransomware-main` project consumes this fork as a pinned Git submodule at
`third_party/B2R2`. Treat that checkout as detached and read-only. Develop,
commit, and push B2R2 changes only from a standalone maintenance clone. Do not
move or replace the submodule without an explicit user request.

1. The research project must pin a verified commit from `topcue/B2R2`.
2. Update and test the B2R2 fork first.
3. Push the verified B2R2 commit only to `origin` (`topcue/B2R2`).
4. Update only the submodule commit pointer in the research project.
5. Record and test the parent-project change before publishing it.

Never point the research submodule directly at an unreviewed upstream commit or
an unpushed local commit. The parent project records the exact reproducible B2R2
version; the fork records the B2R2 implementation history.

## Worker Handoff Checklist

Before changing this fork, a worker must:

- read `AGENTS.md` and this document;
- verify the current branch, worktree, remotes, and push URLs;
- fetch upstream before claiming the fork is current;
- preserve unrelated user changes;
- keep official B2R2 read-only;
- keep new diff implementation inside `ForkDiff` whenever technically
  possible;
- report the exact fork commit that was tested and pushed.
