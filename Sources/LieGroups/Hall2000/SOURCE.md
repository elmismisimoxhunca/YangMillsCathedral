# Hall Lie-group notes source pin

## Identity

- Brian C. Hall, **An Elementary Introduction to Groups and Representations**.
- arXiv:math-ph/0005032v1 (2000).
- Versioned artifact URL: <https://arxiv.org/pdf/math-ph/0005032v1>.
- Retrieved at the UTC time in `FETCH_TIMESTAMP.txt` with
  `curl --proto '=https' --tlsv1.2 -fL --retry 3`.
- Text produced by `pdftotext -layout` 25.03.0.

## Load-bearing locator

Printed p. 115, §7; extracted text lines 6087–6099:

- an ideal `I` satisfies `[X,Y] ∈ I` for every `X ∈ g` and `Y ∈ I`;
- a Lie algebra is simple when its dimension is at least two and its only ideals are zero and the
  whole algebra;
- a semisimple Lie algebra is a direct sum of simple Lie algebras.

This passage is in a section on complex semisimple Lie algebras. The ideal/no-proper-ideal and
non-abelian content is used as authoritative mathematical context for reviewing Mathlib's generic
`LieAlgebra.IsSimple`; it is not by itself a source for every real compact-Lie-algebra theorem.

## Formalization decision

The project will use Mathlib's existing `LieAlgebra.IsSimple`, whose definition requires every Lie
ideal to be bottom or top and explicitly requires non-abelianness. It will not introduce abstract
group simplicity under the same name.

The Hall notes do not interpret the Clay phrase “compact simple gauge group” or decide connectedness
and global form. Those decisions require the Clay source plus the separately pinned gauge-global-
form literature.
