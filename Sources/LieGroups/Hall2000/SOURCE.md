# Hall Lie-group notes source pin

## Identity

- Brian C. Hall, **An Elementary Introduction to Groups and Representations**.
- arXiv:math-ph/0005032v1 (2000).
- Versioned artifact URL: <https://arxiv.org/pdf/math-ph/0005032v1>.
- Retrieved at the UTC time in `FETCH_TIMESTAMP.txt` with
  `curl --proto '=https' --tlsv1.2 -fL --retry 3`.
- Text produced by `pdftotext -layout` 25.03.0.

## Load-bearing locators

Printed p. 15, §§3–3.1; extracted text lines 811–837:

- compact matrix Lie groups are identified with compact subsets in the usual topological sense;
- `O(n)`, `SO(n)`, `U(n)`, `SU(n)`, and `Sp(n)` are listed as compact examples.

Printed p. 16, §4; extracted text lines 860–875:

- connectedness is presented through paths for matrix Lie groups;
- the notes explicitly state that connectedness and path-connectedness agree for matrix Lie groups;
- a disconnected group decomposes into components.

Printed p. 21, §7, Definition 2.14; extracted text lines 1090–1139:

- a Lie group is a differentiable manifold and a group;
- product and inversion are differentiable;
- the local manifold model is finite dimensional.

Printed pp. 81–82, Proposition 5.17; extracted text lines 4410–4444:

- averaging an arbitrary inner product over a compact group's finite-dimensional representation
  with finite Haar measure produces an invariant positive inner product;
- the notes state the result for compact matrix Lie groups and use it to prove complete
  reducibility.

Printed pp. 86–87, §7 and Theorem 5.28; PDF artifact pages 92–93; extracted text lines
4665–4703:

- a morphism intertwines the two representation actions;
- between irreducible real or complex representations, a morphism is zero or an isomorphism;
- an endomorphism of an irreducible complex representation is a complex scalar multiple of the
  identity;
- two nonzero morphisms between irreducible complex representations are scalar multiples of one
  another.

The retained PDF artifact pages 92–93 were visually inspected for this theorem and its hypotheses.
The later matrix-coefficient, character, and Fourier-extraction formulas are project-derived
consequences of Haar averaging, this Schur theorem, trace normalization, and exact matrix unitarity;
they are not quoted as separate Hall theorems.

Printed p. 115, §7; extracted text lines 6087–6099:

- an ideal `I` satisfies `[X,Y] ∈ I` for every `X ∈ g` and `Y ∈ I`;
- a Lie algebra is simple when its dimension is at least two and its only ideals are zero and the
  whole algebra;
- a semisimple Lie algebra is a direct sum of simple Lie algebras.

The last passage is in a section on complex semisimple Lie algebras. The ideal/no-proper-ideal and
non-abelian content is used as authoritative mathematical context for reviewing Mathlib's generic
`LieAlgebra.IsSimple`; it is not by itself a source for every real compact-Lie-algebra theorem.

## Formalization decision

The project uses Mathlib's existing `LieAlgebra.IsSimple`, whose definition requires every Lie
ideal to be bottom or top and explicitly requires non-abelianness. It does not introduce abstract
group simplicity under the same name. Its Lie-group certificate uses a finite-dimensional real
smooth manifold with smooth multiplication and inversion, topological compactness, and explicit
connectedness. Hausdorff and second-countable assumptions make the manifold convention explicit;
they are formalization choices rather than quotations from Hall. Likewise,
`InvariantInnerProductData` asks for the positive adjoint-invariant pairing whose finite-dimensional
compact-representation construction is exemplified by Hall Proposition 5.17; the project does not
claim that the pinned notes prove that construction for its full non-matrix manifold API. The
analytic Haar-intertwiner layer uses Theorem 5.28 only after constructing the exact intertwiner;
trace normalization, coefficient/character orthogonality, and the transposed Fourier-extraction
formula are then derived in Lean rather than attributed verbatim to Hall. For Proposition 5.17, the
real part of the exact averaged form is now packaged as a continuous bilinear map in the original
finite coordinate norm. Finite-dimensional positive-ellipsoid coercivity and Mathlib's inner-core
comparison theorem prove that its induced norm topology is exactly the original coordinate topology.
The resulting topology-compatible normed-additive, complex-normed, and inner-product structures are
exposed as named values without global installation. Every representation matrix is an exact linear
equivalence with inverse at `g⁻¹` and preserves that named averaged norm. These are derived
compatibility and intrinsic-unitarity results. Mathlib's finite-dimensional orthonormal-basis
selection is now reindexed by the original `Fin n` matrix coordinates; the resulting exact linear
equivalence sends selected basis vectors to Kronecker coordinates and carries the averaged pairing
to the standard coordinate Hermitian pairing. Conjugating through that exact equivalence now
constructs a continuous matrix representation with the fixed `Uρ(g)U⁻¹` order and an exact Mathlib
representation equivalence. Transported pairing invariance and a derived column/Kronecker argument
prove the literal equation `star σ(g) * σ(g) = 1`. This completes the finite-coordinate
unitarization consequence of Proposition 5.17 without asserting Peter–Weyl completeness.

The Hall notes do not interpret the Clay phrase “compact simple gauge group” or decide connectedness
and global form. Those decisions use the Clay source plus the separately pinned gauge-global-form
literature. In particular, the project does not require simple connectedness.
