# Hex repo family

`hex-dev` is the development monorepo where new Hex sublibraries are
incubated before they are split out for release. `hex` is the released
aggregate repo; it depends on released split libraries at exact Lake
revisions.

The currently pinned upstream split repos for `hex` are:

- `hex-basic`
- `hex-poly`
- `hex-poly-mathlib`
- `hex-mv-poly`
- `hex-mv-poly-mathlib`
- `hex-matrix`
- `hex-matrix-mathlib`
- `hex-gram-schmidt`
- `hex-gram-schmidt-mathlib`
- `hex-lll`
- `hex-lll-mathlib`

Treat this as the current pinned set, not a permanent exhaustive list:
more sublibraries may be released from `hex-dev` later. Computational
libraries are Mathlib-free; `*-mathlib` repos are the Mathlib bridge
layers and should contain correspondence proofs and Mathlib-facing APIs.
