# Freed principal-bundle and connection source pin

## Identity

- Daniel S. Freed, **Classical Chern-Simons theory, Part 1**.
- arXiv:hep-th/9206021v1 (1992).
- Published in *Advances in Mathematics* 113 (1995), 237–303.
- DOI: <https://doi.org/10.1006/aima.1995.1039>.
- Versioned artifact URL: <https://arxiv.org/pdf/hep-th/9206021v1>.
- Retrieved at the UTC time in `FETCH_TIMESTAMP.txt` with
  `curl --proto '=https' --tlsv1.2 -fL --retry 3`.
- Text produced by `pdftotext -layout` 25.03.0.

## Load-bearing locators

Printed p. 6, §1, equation (1.4); extracted text lines 302–316:

- the Lie algebra is identified with left-invariant vector fields;
- left/right translation and conjugation define the adjoint transformation appearing in the
  Maurer–Cartan equivariance law;
- the Maurer–Cartan equation is recorded.

Printed p. 6, §1; extracted text lines 318–319:

- a principal `G`-bundle `P → X` is described by a manifold `P` with a free right `G`-action and
  quotient `X`.

Printed p. 7, §1; extracted text lines 323–348:

- each fiber is a simply transitive right `G`-space;
- principal bundles are locally trivial.

Printed p. 7, §1; extracted text lines 361–371:

- a principal-bundle map is smooth and equivariant;
- an automorphism over the identity of the base is a gauge transformation.

Printed p. 8, §1; extracted text lines 376–380:

- gauge transformations form a group;
- pullback bundles along smooth base maps are distinguished from gauge automorphisms.

Printed p. 8, §1, equations (1.9)–(1.16); extracted text lines 381–419:

- a connection is a Lie-algebra-valued one-form satisfying vertical normalization and right
  equivariance;
- curvature is `Ω = dΘ + 1/2 [Θ ∧ Θ]` in equation (1.13);
- curvature is horizontal and equivariant;
- equation (1.16) is the Bianchi identity;
- immediately afterward, `d_Θ = d + ad(Θ)` denotes the connection covariant derivative on
  associated-bundle-valued forms.

Printed p. 9, §1, equations (1.18)–(1.19); extracted text lines 434–447:

- bundle maps pull back connections;
- gauge transformations act affinely on connection forms;
- curvature transforms tensorially by the adjoint action.

## Formalization decision

This source will control the reusable principal-bundle, gauge-transformation, principal-connection,
curvature, Bianchi, and gauge-covariance interfaces. Freed's compact-group setting is compatible
with the gauge-group layer, but the general mathematical definitions will be packaged independently
of the eventual Yang–Mills acceptance record.

The paper's subject is Chern–Simons theory. Section 1 explicitly reviews general principal-bundle
connection geometry and is used only for those definitions and identities. It is not evidence for a
four-dimensional Yang–Mills construction, an action functional, quantum existence, or a mass gap.
The paper notes that later parts specialize to connected simply connected groups; the project does
not import that specialization into its global-form policy.

Mathlib currently has no principal-bundle/connection-form/curvature stack matching these locators.
New code must therefore expose freeness, fiber transitivity, local triviality, smooth equivariance,
form degree, and pullback/gauge covariance rather than hiding them in an arbitrary proposition.
The quotient-topology statement for the projection and smoothness of overlap coordinate changes are
derived from the local trivializations, not stored as independent assumptions.
The smooth gauge-automorphism layer requires smoothness of both an invertible total map and its
inverse. This makes the categorical automorphism/diffeomorphism interpretation explicit; it is a
formalization guard, not a claim that Freed separately lists inverse smoothness as an additional
axiom in the cited sentence. The reusable tangent adjoint map is defined, under an explicit `C∞`
Lie-group requirement, as the derivative at the identity of Freed's group conjugation; its identity,
multiplication, and inverse laws are proved before it is used in connection-form equivariance.
Connection-form smoothness is stated locally by evaluation on locally smooth tangent-vector fields,
with an explicit value-coordinate bridge for the intrinsic tangent Lie algebra. This promotes the
same pointwise form satisfying (1.9)–(1.10); it does not construct a connection. Reusable
`lieBracketWedgeOne` infrastructure antisymmetrizes the two bracket orders and proves that the
self-wedge evaluates to twice the pointwise bracket, making the factor `1/2` in (1.13) explicit.
As a reusable project generalization—not a generic formula quoted from Freed—graded infrastructure
now extends a continuous one-form bracket wedge to every continuous `n`-form by the exact omitted-
slot alternating sum and proves degree-one coherence. Equation (1.13) anchors that degree-one
normalization, while (1.16) motivates the one-with-two specialization `[Θ ∧ Ω]`. The existing
smooth coordinate-bracket certificate now proves smooth closure of this exact graded operation by a
finite signed sum. Additivity and real-scalarity in both arguments are derived as reusable project
algebra. The cubic self-bracket is also expanded with the fixed normalization and proved
zero as twice the cyclic Lie Jacobi sum, pointwise and smoothly. A finite-dimensional normed-
coordinate degree-two covariant expression and Bianchi proof are now derived below. A separate
finite-dimensional principal-bundle construction conditionally descends `dω + [Θ∧ω]` from a
supplied ordinary exterior certificate and horizontal/equivariant input, including the same-chain
`D_A F` carrier; no canonical arbitrary-manifold exterior existence or intrinsic Bianchi-zero
result is supplied.
Joint continuity and coordinate smoothness are derived for Mathlib's actual finite-dimensional
Lie-group tangent bracket by transport through the canonical normed model coordinates; the
bracket-wedge is then proved to preserve smooth manifold one-forms.
Mathlib's normed-space `extDeriv`, its nilpotence theorem, and its pullback theorem are packaged as
local-model infrastructure. For arbitrary manifolds, a certified `1 → 2` interface requires a
smooth two-form to satisfy the exact within-set Cartan formula against every pair of local smooth
vector fields and proves compatibility with Mathlib's `extDerivWithin`. As reusable project
infrastructure, a positive-degree certificate now mirrors Mathlib's exact triangular indices and
signs for every `(n+1) → (n+2)` step, including an exact `2 → 3` specialization. At `n = 0`, the
triangular expression is proved equal to the earlier one-form Cartan formula, and bidirectional
conversions preserve the same smooth degree-two derivative carrier. Separately, pinned Mathlib's
within-set `d² = 0` theorem now proves that the positive-degree Cartan expression of the same first
normed-space derivative vanishes, including the exact `1 → 2 → 3` endpoint. The actual
finite-dimensional group Lie-algebra coordinate bracket is now tied to the same bounded bilinear
map used for Mathlib's two-input and self-bracket derivative rules. Its exact continuous
one-with-`n` coordinate wedge is constructed and proved coherent with the intrinsic graded bracket
under the canonical tangent/model equivalence. Fixed-tuple evaluation is packaged continuously,
and the same one-form-valued input derivative now derives the exact four-term derivative of every
self-wedge coefficient. Their exterior alternation is proved to be `-2 • (A ∧ dA)` for the exact
skew coordinate bracket. An explicit operator-norm bound makes the whole wedge operation
continuous bilinear, derives form-valued differentiability from the same input, and identifies the
alternation with Mathlib `extDeriv`. The arbitrary-manifold certificate remains supplied data: existence, chart independence, arbitrary-manifold `d²`, arbitrary-manifold graded Leibniz
transport, and covariant exterior differentiation are not claimed. Given the original
one-form certificate for the same smooth principal connection, `curvatureForm` derives exactly
(1.13).
The set-level `AdjointBundle` implements Freed's displayed `g_P = P ×_G g` as the orbit quotient
for `(p,X)·g = (p·g, Ad(g⁻¹)X)`, including the induced base projection and exact representative
relation. The total carrier now has the induced quotient topology, and its projection is proved a
continuous quotient map onto the already declared base topology. Each existing principal chart
also induces representative-independent set-level coordinates `(π(p), Ad(k)X)` and an inverse based
at group coordinate `1`, with both local inverse laws proved. Smoothness of the parameter-dependent
adjoint map in model coordinates is derived from Mathlib's `ContMDiffAt.mfderiv`; the retained
`ContinuousLieGroupAdjointData` interface therefore has a canonical general inhabitant. Each chart
packages as an open partial homeomorphism using that derived regularity and promotes exactly to
Mathlib's generic `Bundle.Trivialization` interface on the same quotient carrier and topology.
The ordered associated overlap is then derived exactly as `(b,X) ↦ (b, Ad(k₁₂(b))X)` from the
actual principal transition, with inverse and fiberwise real-linearity laws. Its source is proved to
be exactly the intersection of the two base domains times the whole fiber. Its model-coordinate
formula and forward/inverse operator-equivalence families are proved `C∞` by composing the
designated smooth principal overlap with the derived smooth adjoint action. The coordinate adjoint is also packaged as a continuous linear equivalence with
smooth forward and inverse operator families. After explicit transport through the canonical
tangent-model equivalence, the
promoted charts form a named covering charted-space atlas on the same quotient topology. Their
pairwise changes are proved compatible with Mathlib's smooth fiberwise-linear groupoid, yielding a
named `C∞` manifold structure on the same quotient carrier and topology. No global atlas/manifold
instance is installed. The quotient fibers are additionally packaged as a dependent family with a
base-preserving carrier equivalence back to the same quotient. Its named topology is then pulled
back from the quotient, making that equivalence a base-preserving homeomorphism without installing
a competing global topology instance. Every dependent fiber then receives named real vector-space
structures transported through the explicitly selected associated coordinate. Every other
designated associated coordinate is then proved to differ by the exact adjoint linear transition.
The established quotient trivializations are then transported exactly across the base-preserving
total-space homeomorphism, with per-fiber topologies induced from selected coordinates. `FiberBundle`
fiber inclusions are then proved inducing and the preserved topology plus transported atlas are
packaged as a named Mathlib `FiberBundle`. Every transported chart is proved linear, its Mathlib
coordinate change is identified exactly with the derived adjoint operator, and operator-norm
continuity packages a named `VectorBundle`. The same exact operator families package a named
Mathlib `ContMDiffVectorBundle ∞` mixin; no global bundle instance is installed. Dependent sections
and smoothness in that exact atlas are defined, with a selected-coordinate criterion and smooth zero
section. Pointwise adjoint-bundle-valued differential forms are now typed as continuous alternating
maps into the actual dependent quotient fiber, with exact designated coordinates. Smoothness is
then defined by evaluation on locally smooth tangent fields in every designated exact chart; the
smooth zero form is derived. Degree-zero forms are proved exactly equivalent to dependent sections,
including smoothness in both presentations. Every designated principal chart now supplies a smooth
local section and a tangent lift proved right-inverse to the actual projection differential. The
lift is identified with Mathlib's tangent map within the chart domain and proved to carry smooth base
tangent fields to smooth fields along the local section. Reusable calculus now proves smooth form
evaluation along a smooth map whenever those along-map fields admit explicit ambient smooth
extensions. Such extensions are now constructed for the exact local tangent lifts by transporting a
base field with zero group component through the inverse principal chart. Consequently, every
smooth fixed-value principal form is now proved to evaluate smoothly on the exact local lifts.
Using horizontality and right adjoint equivariance, this evaluation is transported across arbitrary
designated presentations to package a smooth adjoint-bundle-valued descended two-form. Applied to
the indexed structure certificate, this now packages smooth descent of the exact derived curvature. Horizontality
is proved to make two-form evaluation independent of tangent-lift choices at a fixed
total-space point. Right adjoint equivariance is then proved to identify the resulting values in the
actual adjoint orbit quotient across right-related representatives, including replacement lifts with
matching projections. A pointwise dependent-fiber base form is now constructed from the selected
local section/lifts and proved to agree with all such right-related presentations. This construction
is specialized to the exact curvature derived from one connection and exterior-derivative datum,
with presentation independence supplied by its indexed structure certificate. The exact pointwise
base curvature is now proved smooth and packaged without changing its carrier. The separately
specified adjoint-invariant Lie-algebra pairing is transported to the actual adjoint fibers,
proved independent of every designated chart, and packaged as a bilinear map without changing its
exact quotient-coherent values.
`PrincipalTwoForm.IsHorizontal`, `.IsRightAdEquivariant`, and the connection-indexed
`PrincipalCurvatureStructureCertificate` state (1.15) and (1.14) intrinsically without accepting an
unrelated curvature field. This is a requirement surface: automatic derivation from the current
Cartan certificate and connection laws remains pending. The existing same-connection derivative on
adjoint sections is now canonically packaged as the degree-zero-to-degree-one endpoint of `d_Θ`,
with no new witness and with the exact local `dσ + [A,σ]` formula retained. The separately stored
`C∞` derivative regularity now derives smoothness of this exact degree-one output for every smooth
degree-zero input through smooth bundle-map evaluation. Separately, the local normed-coordinate
curvature and degree-two covariant exterior expression are derived from one twice differentiable
one-form, and their Bianchi identity follows from `d²`, self-wedge Leibniz, and Jacobi. Within-set
versions retain one explicit set together with its regularity, uniqueness, membership, and
closure/interior hypotheses and agree with the global definitions on `univ`. Fixed-value manifold
forms now have separate raw unrestricted and explicit within-set normed-coordinate pullbacks.
Inverse extended charts use corner-aware `mfderivWithin` on the exact model range, with target-local
derivative invertibility and canonical bracket-wedge carrier coherence. For finite-dimensional
principal total-space models, stored intrinsic connection smoothness now derives target-wide `C∞`
regularity of the exact coordinate one-form. That regularity lemma alone asserts no exterior
naturality or geometry outside the chart target; the subsequent Cartan-transport theorem supplies
naturality on the target.
The exact principal connection, its indexed derivative certificate, and curvature derived from both
now satisfy (1.13) after the same within-set or inverse-chart coordinate transport. An exact
naturality predicate separates inverse-chart tangent transport on the model range from exterior
calculus on the actual chart target. Reusable mathematics proves inverse-chart Cartan transport for
arbitrary differentiable fixed-value coordinate one-forms using the within-chain rule, exact tangent
cancellation, Mathlib Lie-bracket pullback, and vanishing constant-coordinate brackets. In the
finite-dimensional principal specialization, intrinsic smoothness discharges differentiability and
derives the Cartan equality, full exterior naturality, and the exact same-connection coordinate
Bianchi identity at every actual target point without accepting naturality, regularity, or Bianchi
witnesses. The exact smooth adjoint-bundle curvature descent is additionally tied chartwise to that
same representative: its designated base-chart coordinate is the exact principal curvature on the
local section and tangent lifts, while the representative satisfies coordinate Bianchi. This does
not construct an intrinsic adjoint-valued three-form. Freed's p. 9 pullback statement now anchors an
exact gauge-automorphism pullback of principal connections: tangent naturality derives vertical
normalization and right equivariance, transported test fields derive smoothness, and identity plus
composition expose the contravariant pullback order. Smooth pullback in every degree and exact
Lie-bracket-wedge naturality now prove that the curvature formula assembled from the pulled
derivative carrier equals the pullback of the original curvature. Reusable diffeomorphism mathematics now transports the complete within-set
Cartan certificate under the explicit complete-source-model premise required by Mathlib's public
Lie-bracket naturality theorem; finite-dimensional principal total-space models derive that premise.
The canonical transformed principal curvature is therefore proved equal to the total-space pullback
of the original exact curvature. Torsor uniqueness now defines the associated function `g_ϕ` by
`ϕ(p)=p·g_ϕ(p)` and derives its right-action conjugation law. Differentiated projection preservation,
horizontality, and right equivariance then prove the evaluated local curvature identity with the
exact factor `Ad(g_ϕ(p)⁻¹)`. The selected associated function is now identified with smooth
principal-chart coordinates on local sections; chart conjugation and atlas coverage derive its
global `C∞` regularity. Left Maurer–Cartan trivialization and the differentiated variable principal
action now derive the evaluated affine connection law with the exact inverse adjoint factor, plus
sign, and inhomogeneous `g_ϕ⁻¹dg_ϕ` term. Given any exact smooth principal connection, the affine
identity and joint adjoint regularity derive a smooth-form bundle with the unchanged Maurer–Cartan
carrier. The original curvature structure certificate now canonically transports to the gauge-pulled
curvature. Pointwise adjoint-bundle descent is expressed by the exact `Ad(g_ϕ⁻¹)` coefficient and an
equivalent inverse-shifted principal representative, without asserting equality to the original
adjoint-valued curvature. The covariant action `[p,X] ↦ [ϕ(p),X]` is now constructed on the actual
adjoint quotient and dependent fibers, and transformed pointwise/smooth-descended curvature
evaluations are proved to use its inverse. In the selected fiber coordinate the forward action is
exactly `Ad(g_ϕ)`, so every fixed fiber action is bundled as a continuous real-linear equivalence
with exact inverse-gauge carrier. Quotient continuity and the exact quotient/dependent carrier bridge
then produce a base-preserving dependent-total-space homeomorphism whose fiber restrictions are
those continuous-linear equivalences. The exact quotient-chart formula
`(b,X) ↦ (b,Ad(g_ϕ(s(b)))X)` now derives global forward/inverse `C∞` regularity and a quotient
Diffeomorph. In the named dependent smooth-vector-bundle structure the same formula derives a
base-preserving total-space `C∞` diffeomorphism whose fixed-fiber restrictions are the exact
continuous-linear equivalences, completing the layered smooth bundle-automorphism packaging. The
same forward coordinate law and adjoint invariance prove simultaneous gauge invariance of the exact
descended fiber pairing and its quadratic value. Combined with inverse-action curvature covariance,
this derives pointwise invariance of the chosen and basis-independent canonical curvature densities
for the exact pulled chain. Exact integrability transport preserving the designated measure and
coupling then derives invariance of the integrated relative-to-measure action for vertical gauge
transformations over the identity base map. Smooth tangent-map calculus now proves direct,
connection-independent smoothness of the exact associated Maurer–Cartan pullback while retaining
the independent affine-difference proof. On the universal group form, the exact invariant-field
Cartan calculation fixes the candidate sign and normalization `-1/2[θ∧θ]`; the associated form is identified with its pullback and
the smooth candidate is packaged. Field-extension independence is now proved in normed spaces,
exact centered-chart coordinates, and intrinsically conditional on an existing certificate.
Arbitrary smooth fields now transport through the exact corner-aware centered chart, and explicit
coordinate-form differentiability derives intrinsic extension independence. Finite-dimensional
basis reconstruction now derives that complete coordinate-form regularity generically, yielding
intrinsic extension independence for admissible smooth fields. This constructs a genuine universal
exterior-derivative certificate and proves the displayed group-level Maurer–Cartan equation.
The associated smooth candidate is proved exactly equal to the raw pullback of that certified
derivative. Exact chart-safe carrier and locality bridges construct the arbitrary-smooth-map Cartan
certificate from the existing smooth pullback packages in finite-dimensional models, certifying the
candidate as `dα` and deriving the associated normalized equation. An independently defined quantum gauge
action on observable operators and
broader-observable invariance remain pending. The finite `1`, `F²`, `(F²)²` interpretation records
do transport to the exact pulled chain with unchanged classical carriers, quantum family/labels,
and anti-collapse witnesses; this is deliberately only same-family transport. Arbitrary-map/
two-set exterior naturality, a canonical arbitrary-manifold positive-degree operator, an intrinsic
descended adjoint-bundle Bianchi theorem, and full gauge covariance remain pending.
