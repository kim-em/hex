# Hex repo family

`hex-dev` is the development monorepo where new Hex sublibraries are
incubated before they are split out for release. `hex` is the released
aggregate repo; it depends on released split libraries at exact Lake
revisions.

The currently pinned upstream split repos for `hex` are:

- `hex-basic`
- `hex-arith`
- `hex-primality`
- `hex-primality-mathlib`
- `hex-poly`
- `hex-mv-poly`
- `hex-mod-arith`
- `hex-sparse-poly`
- `hex-poly-mathlib`
- `hex-sparse-poly-mathlib`
- `hex-mv-poly-mathlib`
- `hex-poly-fp`
- `hex-poly-z`
- `hex-mod-arith-mathlib`
- `hex-poly-fp-mathlib`
- `hex-gfq-ring`
- `hex-hensel`
- `hex-poly-z-mathlib`
- `hex-hensel-mathlib`
- `hex-roots`
- `hex-real-roots`
- `hex-roots-mathlib`
- `hex-real-roots-mathlib`
- `hex-matrix`
- `hex-row-reduce`
- `hex-berlekamp`
- `hex-conway`
- `hex-gfq-field`
- `hex-gf2`
- `hex-gf2-mathlib`
- `hex-gfq`
- `hex-gfq-mathlib`
- `hex-determinant`
- `hex-bareiss`
- `hex-matrix-mathlib`
- `hex-row-reduce-mathlib`
- `hex-determinant-mathlib`
- `hex-bareiss-mathlib`
- `hex-berlekamp-mathlib`
- `hex-gram-schmidt`
- `hex-gram-schmidt-mathlib`
- `hex-lll`
- `hex-berlekamp-zassenhaus`
- `hex-lll-mathlib`
- `hex-berlekamp-zassenhaus-mathlib`
- `hex-graph-iso`
- `hex-graph-iso-mathlib`
- `hex-resultant`
- `hex-resultant-mathlib`
- `hex-number-field`
- `hex-number-field-mathlib`
- `hex-number-field-tower`
- `hex-number-field-tower-mathlib`
- `hex-rcf`

Treat this as the current pinned set, not a permanent exhaustive list:
more sublibraries may be released from `hex-dev` later. Computational
libraries are Mathlib-free; `*-mathlib` repos are the Mathlib bridge
layers and should contain correspondence proofs and Mathlib-facing APIs.
