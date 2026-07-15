# Declaration-level source map

This ledger maps source obligations to Lean declarations. A blank declaration means the
requirement has not yet been formalized; it must not be inferred from roadmap prose.

## Clay/Jaffe–Witten source of record

Artifact: `Sources/Clay/yangmills_official.pdf`
Searchable extraction: `Sources/Clay/yangmills_official.txt`

| Source locator | Requirement | Classification | Lean declaration | Status / decision |
|---|---|---|---|---|
| p. 5 §3; text 222–240 | Hilbert space, Poincaré representation, self-adjoint translation generators, invariant unique vacuum, positive energy, covariance and locality | Model requirement | — | Pending Wightman/Poincaré sources and definitions |
| p. 5 §3; text 241–253 | Relation between Euclidean and Lorentzian axiom schemes through reflection positivity/reconstruction | Bridge | — | Pending corrected OS source pin; no definitional identification allowed |
| p. 6 §4; text 263–266 | 4D QFT with local operators corresponding to gauge-invariant local curvature polynomials and covariant derivatives | Model requirement | — | Pending geometry and renormalized observable semantics |
| p. 6 §4; footnote 1; text 298–304 | Renormalization prevents a natural one-to-one classical-polynomial/quantum-field correspondence | Formalization constraint | — | Raw syntactic injectivity is forbidden as canonical semantics |
| p. 6 §4; text 267–271 | Short-distance agreement with asymptotic freedom and perturbative renormalization | Model requirement | — | Pending primary renormalization sources and precise distributional formulation |
| p. 6 §4; text 269–271 | Stress tensor | Model requirement | — | Pending source and semantics |
| p. 6 §4; text 269–271 | Operator-product expansion with prescribed local singularities | Model requirement | — | Pending source and semantics |
| p. 6 §4; text 272–276 | Poincaré-invariant zero-energy vacuum, nonnegative Hamiltonian spectrum and no spectrum in `(0, Δ)` | Model requirement / definition | — | Pending physical translation/PVM semantics |
| p. 6 §4; text 275–276 | Supremum of admissible gaps is finite mass | Model requirement / definition | — | Pending non-vacuous supremum definition |
| p. 6 §4; text 277–280 | For every compact simple gauge group, a nontrivial QFT on `ℝ⁴` exists and has positive gap | Final acceptance proposition | — | Pending all lower layers; no inhabitant asserted |
| p. 6 §4; text 279–280 | Axiomatic properties at least as strong as references [45, 35] | Comparative requirement | — | Pending verified Wightman and corrected OS source maps |

## Non-source project declarations

| Lean declaration | Purpose | Authority | Axiom status |
|---|---|---|---|
| `YangMills.Audit.audit_yang_mills_axioms` command | Kernel-level rejection of `sorryAx` and project-defined axioms | Project validation infrastructure; uses `Lean.collectAxioms` | Checked by the root build and mutation fixtures |

Every future canonical physical declaration must be added here in the same commit that introduces
it. “Pending” rows are obligations, not accepted placeholder fields.
