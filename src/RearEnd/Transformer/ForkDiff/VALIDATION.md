# Fork diff validation

This document records the external oracle and the limits of the fork diff
validation. It is intended to keep future maintenance independent of chat
history.

## Ground truth

The algorithm reference is the standalone Git xdiff repository:

- repository: `https://github.com/libgit2/xdiff.git`
- validated reference: `c46ae8dd20ed6f4fae8fb9a30cad6932c85269fc`
- reference date: 2026-05-02

That repository extracts the xdiff library used by Git. It is a read-only
reference, not a B2R2 dependency, and none of its source is vendored here. The
reference clone used during the 2026-09-10 audit had its push URL disabled.
Future workers must review and preserve the reference project's licenses before
copying any code; black-box oracle tests do not require copying it.

The automated oracle invokes the installed Git command with `--no-index` and
`--numstat`. Each byte is encoded as one hexadecimal text line so that Git and
B2R2 compare the same token sequence. Myers uses `--minimal`; Histogram uses
Git's `--diff-algorithm=histogram` behavior.

## Current coverage

`src/RearEnd/Transformer.Tests/Diff.Tests.fs` verifies:

- empty, identical, insertion, repeated, crossed, and reversed Myers cases;
- deterministic randomized Myers results against an independent LCS oracle;
- Myers edit metrics against Git xdiff;
- deterministic randomized Histogram metrics against Git xdiff;
- Histogram fallback when every common value exceeds its occurrence limit;
- a 100,000-element repeated-input regression case;
- byte, text, instruction, and section presentation behavior;
- JSON, summary, side-by-side, and action registration behavior.

The Git oracle checks edit metrics rather than exact hunk placement. Multiple
valid shortest edit scripts may choose different equal tokens, so presentation
tie-breaking needs separate golden tests. The large-input test rejects gross
complexity regressions without imposing a machine-dependent timing threshold.

## Implementation findings

The 2026-09-10 audit found and corrected these issues:

- Myers input preparation repeatedly appended to immutable arrays, causing
  quadratic copying before the actual comparison.
- Common-prefix and common-suffix trimming mishandled the fully consumed side
  and retained unnecessary work.
- Myers and Histogram traversal used input-dependent call-stack recursion.
- Histogram rescanned the entire opposite range for every candidate.
- Histogram selected a single rare token instead of Git's extended common
  region, which over-reported edits on repeated inputs.

The current implementation preallocates its filtered inputs, indexes Histogram
positions, expands candidate common regions, and uses explicit work stacks.
