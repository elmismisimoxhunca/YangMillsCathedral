# Supplied literature ingestion and definition audit

**Bundle location inspected:** `/root/*.pdf`  
**Bundle date:** files supplied together on 2026-07-19  
**Audit status:** all 33 PDFs inventoried; 7 were byte-identical to already canonical artifacts; 26 distinct artifacts are now retained or added to an existing source record.  
**Extraction policy:** 31 PDFs have native `pdftotext -layout` extractions. The image-only Atiyah–Hitchin–Singer 1978 and Atiyah–Bott 1983 scans use the project Mathpix extractor, calibrated printed-page offsets, provenance/line sidecars, normalized per-page machine drafts, and retained independent visual adjudications. Machine drafts are not silently treated as citable text.

The exact filename/SHA-256/size/page/title/retained-path inventory is
`docs/SUPPLIED_SOURCE_INVENTORY.tsv`. A hash-coverage check confirms all 33 supplied PDFs occur
byte-for-byte under `Sources/`; a fresh extraction comparison confirms all 31 native-text PDFs
reproduce their retained `pdftotext -layout` output exactly.

This audit distinguishes byte ingestion from mathematical use. A manifest proves only that retained
bytes have not changed. A source becomes load-bearing for a declaration only after exact locators,
scope qualifications, and the declaration classification are entered in `docs/SOURCE_MAP.md`.

## 1. Complete 33-file inventory

| Supplied file | Canonical disposition | Principal audit role |
|---|---|---|
| `0005032v1.pdf` | Already canonical, byte-identical to `Sources/LieGroups/Hall2000/hall_lie_groups_notes.pdf` | Finite-dimensional Lie-group/Lie-algebra background |
| `0101239v1.pdf` | `Sources/TwoDimensional/Levy2003/` | Discrete/continuum compact-surface Yang–Mills measure and random holonomy |
| `1305.0318v5.pdf` | Already canonical, byte-identical Aharony–Seiberg–Tachikawa artifact | Global gauge-group form and line-operator warning |
| `9206021v1.pdf` | Already canonical, byte-identical Freed artifact | Principal connection/curvature/gauge/Bianchi spine |
| `ambrose1944.pdf` | `Sources/AxiomaticQFT/Ambrose1944/` | Original spectral resolution/SNAG background |
| `atiyah1978.pdf` | `Sources/GaugeGeometry/AtiyahHitchinSinger1978/` | Four-dimensional Hodge splitting and self-duality consistency |
| `atiyah1983.pdf` | `Sources/GaugeGeometry/AtiyahBott1983/` | Classical Yang–Mills geometry over Riemann surfaces |
| `bargmann1947.pdf` | `Sources/AxiomaticQFT/Bargmann1947/` | Lorentz representation/cover audit |
| `barnich2000.pdf` | `Sources/Renormalization/BarnichBrandtHenneaux2000/` | Local BRST cohomology and local operator grammar |
| `callan1970.pdf` | `Sources/Renormalization/Callan1970/` | General scale-Ward/RG background only |
| `caswell1974.pdf` | `Sources/Renormalization/Caswell1974/` | Optional two-loop beta-function cross-check |
| `collins1977.pdf` | Added to `Sources/Renormalization/CollinsDuncanJoglekar1977/` alongside the KEK preprint | Published trace-anomaly/mixing formula and locator cross-check |
| `driver1989.pdf` | `Sources/TwoDimensional/Driver1989/` | Rigorous planar YM2, heat-kernel expectations, Villain/Wilson lattice convergence |
| `gross1989.pdf` | `Sources/TwoDimensional/GrossKingSengupta1989/` | Rigorous stochastic continuum YM2 and loop invariance |
| `hall2015.pdf` | `Sources/LieGroups/Hall2015/` | Modern matrix/compact Lie-group and `SL(2,ℂ)` background |
| `hollands2008.pdf` | `Sources/Renormalization/Hollands2008/` | Perturbative BRST/local-covariance and renormalized-field audit |
| `hollands2012.pdf` | `Sources/Renormalization/HollandsKopper2012/` | Perturbative scalar OPE convergence; not a Yang–Mills theorem |
| `husemoller1994.pdf` | `Sources/GaugeGeometry/Husemoller1994/` | Fibre/principal/associated bundles and structure-group changes |
| `joglekar1976.pdf` | `Sources/Renormalization/JoglekarLee1976/` | Gauge-invariant/BRST/EOM triangular operator mixing |
| `jost2017.pdf` | `Sources/GaugeGeometry/Jost2017/` | Curvature, Bianchi, Hodge pairing, YM functional and gauge invariance |
| `kluberg-stern1975.pdf` | `Sources/Renormalization/KlubergSternZuber1975/` | Background-field gauge-invariant operator renormalization |
| `MEMO_126_600.E.pdf` | `Sources/TwoDimensional/Sengupta1997/` | Purchased compact-surface YM measure/holonomy monograph |
| `mfm-31-5.pdf` | `Sources/AxiomaticQFT/HallWightman1957/` | Extended-tube invariant analytic theorem |
| `osterwalder1973 (2).pdf` | Already canonical, byte-identical OS-I scan | OS-I axioms/source topology |
| `osterwalder1975 (1).pdf` | Already canonical, byte-identical OS-II scan | Correcting OS-II priority |
| `singer1978.pdf` | `Sources/GaugeGeometry/Singer1978/` | Gribov obstruction; negative audit against global gauge slices |
| `symanzik1970.pdf` | `Sources/Renormalization/Symanzik1970/` | Short-distance power counting and RG asymptotics |
| `wightman1956 (1).pdf` | Already canonical, byte-identical Wightman scan | Vacuum distributions/reconstruction origin |
| `wilson1972.pdf` | `Sources/Renormalization/WilsonZimmermann1972/` | OPE/composite-field bridge |
| `witten1991.pdf` | `Sources/TwoDimensional/Witten1991/` | Exact 2D heat-kernel/character sewing formulas; physical cross-check |
| `yang1954.pdf` | `Sources/GaugeGeometry/YangMills1954/` | Historical non-Abelian local field-strength/action formulas |
| `yangmills.pdf` | Already canonical, byte-identical Clay artifact | Official problem statement |
| `zimmermann1973.pdf` | `Sources/Renormalization/Zimmermann1973/` | Normal products, subtraction degree, Zimmermann identities |

## 2. OCR and visual-adjudication audit

Only `atiyah1978.pdf` and `atiyah1983.pdf` lack useful native body text. Their retained `ocr/`
directories include Mathpix submission/provenance records, raw MMD, line-confidence JSON, TeX zip,
calibrated per-printed-page drafts, and independent visual reads/adjudications. The extractor selftest
passed after import.

The independent audit found unflagged mathematical OCR errors, proving that confidence thresholds
alone are insufficient. Examples include `A⁰(E)` read as `A°(E)`, a representation `ρ` read as `p`,
loss of tildes on lifted vector fields, and incorrect bundle targets. Consequently:

- normalized pages remain `layer: machine-draft`;
- only explicitly adjudicated passages may be quoted;
- raw OCR never overrides the scan;
- the calibrated page-offset tables are authoritative only on their verified ranges.

Adjudicated load-bearing passages currently include AHS printed p. 427 for
`α∧*β=(α,β)ω`, `*²=(-1)^l`, and `Λ²=Λ²₊⊕Λ²₋`; AHS p. 430 for principal curvature and associated
bundle formulas subject to recorded corrections; Atiyah–Bott p. 548 for curvature and the
Yang–Mills functional; and pp. 551–552 for connection/curvature variation subject to the explicit
adjudication corrections.

## 3. Audit of current axioms and definitions

### Validated without semantic change

- **Principal geometry:** Freed remains the canonical source for connection normalization,
  right-equivariance, curvature, and Bianchi. Jost independently confirms local
  `F=dA+A∧A`, `DF=0`, invariant pairing, the Yang–Mills functional, curvature covariance, and action
  invariance. Husemoller corroborates the topological bundle/trivialization/transition layer.
- **Gauge-group identity:** Hall 2015 corroborates compact/matrix Lie-group and semisimple-algebra
  conventions but does not silently extend matrix results to every project manifold carrier.
  Aharony–Seiberg–Tachikawa confirms that the exact global group `G` cannot be replaced by its Lie
  algebra or universal cover.
- **Trace anomaly:** the supplied published Collins–Duncan–Joglekar article agrees with the retained
  KEK preprint. The current Lean interface correctly restricts the simple beta-function `F²` formula
  to an explicit nonempty physical/on-shell/nonzero-momentum matrix-element selection and keeps
  unrestricted BRST/EOM/mixing terms out of that equality.
- **Weak OPE:** Wilson–Zimmermann supports finite local-field asymptotic organization and the need
  for renormalized composite fields. The current generic weak OPE is a valid supplied interface but
  is not a calculated Yang–Mills perturbative expansion.
- **PVM/spectrum:** Ambrose supplies original spectral-resolution background, while the visually
  checked Streater–Wightman source remains the closer canonical source for the exact physical joint
  momentum PVM used by the project.
- **No global gauge fixing is assumed:** no current canonical declaration was found that chooses one
  representative globally. Singer's Corollary 4 rules out a continuous global gauge choice in its
  stated `S⁴` setting (with the analogous `S³` conclusion); this is a strong scoped warning against
  adding such data, not an unrestricted theorem for every project carrier.

### Definitions shown to be intentionally incomplete

- **2D continuum:** the current `TwoDimensionalKinematicNondegeneracyData` and finite plaquette are
  only kinematic/cutoff evidence. Driver, Gross–King–Sengupta, Sengupta, Lévy, and Witten now provide
  sufficient retained literature for a genuine source-specific 2D probability/holonomy acceptance
  layer. No present theorem is contradicted, but the completion audit must no longer describe the
  source as unavailable.
- **Operator grammar and mixing:** Joglekar–Lee, Zimmermann, Barnich–Brandt–Henneaux, and
  Wilson–Zimmermann show that the natural next layer is a typed local jet/composite grammar modulo
  total derivatives, BRST-exact and EOM sectors, with finite subtraction-degree bases and a
  triangular mixing matrix. The existing `1`, `F²`, `(F²)ⁿ` family is correctly documented as a
  narrow fragment, not a complete grammar.
- **Perturbative remainders:** Symanzik supports power-counting/RG constraints. Hollands–Kopper gives
  quantitative OPE convergence only for massive Euclidean scalar theory at fixed perturbative
  order and cannot be promoted to Yang–Mills. Hollands 2008 supplies a modern perturbative
  BRST/local-covariance audit but no nonperturbative 4D construction.
- **Hodge and volume:** Jost and AHS now supply the literature needed for a general Hodge-star/
  metric-volume acceptance interface and its 4D specialization. The missing obstacle is Lean/
  Mathlib infrastructure and proof, not source acquisition.
- **Poincaré construction:** Hall 2015, Bargmann, and the already retained Streater–Wightman book
  supply the literature for the `SL(2,ℂ)`/proper-Lorentz relationship and affine law. Constructing
  the exact topological group and cover remains formal mathematics.
- **Extended tube:** Hall–Wightman 1957 is now retained. The existing extended-tube geometry remains
  valid, but derivation of the analytic continuation theorem should use this source rather than
  remain only a supplied requirement.

### Corrections and scope fences

1. Driver's verified DOI is `10.1007/BF01218586`; a scout-produced alternative identifier was
   rejected against the repository's Crossref metadata and supplied article identity.
2. Driver constructs a gauge-fixed probability law whose physical interpretation is asserted on
   gauge-invariant functions; do not call it a canonical measure on smooth connections modulo gauge.
3. Driver, not Gross–King–Sengupta or Witten, supplies the stated Villain/Wilson lattice-observable
   convergence theorems.
4. Driver PDF p. 6 / printed p. 580 and PDF p. 9 / printed p. 583 were visually adjudicated on
   2026-07-21 for Definitions 3.1/3.8. Definition 3.1 visibly requires a continuous height in the
   horizontal graph `(t, σ(t))`; Definition 3.8 visibly requires a finite decomposition into
   vertical line segments and `C¹`-horizontal curves. The retained native extraction agrees,
   including the superscript `1`. Affine-speed parameterizations in Lean are a project
   strengthening, not source wording.
5. Driver PDF p. 17 / printed p. 591 was visually adjudicated on 2026-07-21 for Definitions
   6.1/6.2. The page visibly requires piecewise `C¹` curves, finitely many connected components of
   `ℝ² \ (S ∪ {x-axis})`, Definition-3.8 admissibility, no immediate retracing, a finite directed
   graph on a discrete planar vertex set, endpoint-only crossings, endpoint coherence, and an
   admissible bond collection. The retained native extraction agrees.
6. Driver PDF pp. 15–16 / printed pp. 589–590 were visually adjudicated on 2026-07-21 for
   Definition 5.1 and the exact `D_T g` measure. They visibly define a tree by orientation stability
   and absence of a nonempty closed path using distinct unoriented bonds, with connectedness as a
   separate strengthening; tree bonds receive identity point mass and all others receive Haar.
7. Driver PDF p. 18 / printed p. 592 was visually adjudicated on 2026-07-21 for Definition 6.3
   and Theorem 6.4. It visibly requires gauge transformations to fix the distinguished origin,
   states the area-indexed boundary-holonomy product-Haar expectation, asserts independence from
   all boundary choices, and separately states invariance under freezing any tree. The current Lean
   interface covers the exact conditional coordinate-zero restricted-gauge clause and quantifies
   choice independence over the full carrier of valid simultaneous connected-component
   presentations. The universal tree-freezing strengthening now uses Definition 5.1's exact
   no-loop predicate and the exact mixed identity-Dirac/Haar product.
8. Driver PDF p. 21 / printed p. 595 was visually adjudicated on 2026-07-21 for Theorem
   6.6. It visibly quantifies over a gauge-invariant function on a BC graph and equates its
   continuum holonomy expectation with Haar integration weighted by the product of `Q` at exact
   bounded-region areas and boundary holonomies. The proof labels it the BC special case of
   Theorem 6.4. The Lean interface restricts to measurable/integrable complex functions and has
   both a Jordan-boundary subclass and a strengthened embedded-arc BC layer with exact bridge
   multiplicity; no graph or law instance is constructed.
9. Driver PDF p. 8 / printed p. 582 and PDF pp. 23–24 / printed pp. 597–598 were
   visually adjudicated on 2026-07-21 for Proposition 3.5, Definition 7.1, equations
   (7.1)–(7.4), and Theorem 7.2. The visible formulas confirm later-on-the-left path multiplication,
   the complete action contract, the vertical-plus-x-axis axial tree, finite plaquette products,
   delta boundary conditions, free-boundary formulas, weak limits, boundary independence, and the
   finite-cylinder restriction conclusion. The current layer locks plaquette order through the
   reusable finite-oriented-word evaluator but constructs no finite-volume measure.
10. Driver PDF p. 27 / printed p. 601 was visually adjudicated on 2026-07-21 for Definition 8.1.
   The page visibly fixes the nearest-neighbor directed graph on `εℤ²`, requires approximating
   graph edges to be paths in it, gives bond/region surjections, requires symmetric-difference area
   of order `ε`, and preserves admissible boundary sums. The Lean layer formalizes exact positive-
   spacing nearest-neighbor path geometry and an uninhabited Definition 8.1 family on the project's
   strengthened embedded-arc subclass, with surjective edge/face maps, explicit uniform area order,
   nonvacuous universal facewise boundary-presentation transport, and explicit loop-subdivision debt;
   Driver's Villain action is now the smooth strictly-positive real representative of the unchanged
   semigroup density at exact time `ε²`, requiring the exact Definition 4.7
   `∂ₜQ = 1/2 ΔQ` chain, an initial-identity generated operator semigroup, and Driver's displayed
   convolution-kernel identity; its full inherited action contract, including real Haar-integral
   normalization, and normalized nonzero single-plaquette Haar-density measure are derived.
   Driver's Wilson action now uses the matrix-trace character of an actual continuous nonzero finite-
   dimensional unitary representation and positive source-indexed normalizers tied to the
   unnormalized Haar integral; its inherited real action contract is derived. Axial field measures
   and convergence remain open. Definition 7.1 is packaged once with exact Villain/Wilson adapters
   and a separately labeled constant-one nonvacuity inhabitant. The infinite directed `εℤ²` bond,
   reverse-inversion configuration, and exact vertical-plus-x-axis axial-tree carriers are explicit;
   sites embed at `(εm, εn)`, bonds have signed physical `ε` steps, coordinate projections are
   measurable, and a concrete nonidentity off-axis axial configuration proves non-subsingletonness,
   but no lattice field measure is supplied. Exact elementary plaquettes now have physically scaled
   closed counterclockwise boundaries and measurable/nonzero finite common-action products; finite-
   volume normalizers remain absent at the exact square-box level. Generic finite axial
   presentations now define exact partition functions and normalized finite product-Haar density
   measures from orientation-disjoint off-tree coordinates, measurable finite-support extensions,
   and complete selected-plaquette non-tree boundary-coordinate coverage;
   their same-extension pushforwards are normalized nonzero measures on the exact infinite axial
   carrier with represented-coordinate marginal identities. They are explicitly not yet Driver's
   square boxes or constructed infinite-volume limits. An uninhabited projective-sequence contract
   now requires nested finite-law pushforward plus exhaustive bonds/plaquettes, and an infinite axial
   probability interface requires all finite-coordinate cylinder laws exactly. Exact positive-radius
   centered square-box plaquette/off-axis-coordinate sets are now separately defined with literal
   radius nesting and complete non-tree boundary coverage. Their concrete generic-presentation
   adapter now has exact coordinate/plaquette subtypes and a measurable reverse/identity extension;
   compact action bounds and strict positivity now prove the exact box partition functions finite
   and nonzero, constructing normalized finite-coordinate and same-extension pushforward measures.
   Literal successor box inclusions/restriction are constructed and an uninhabited exact consecutive
   pushforward obligation is stated. Driver's distinct `Aₙ`, `Aₙ₋₁`, `Bₙ`, `B̄ₙ`, and frozen
   `Bₙᶜ` sets are represented with exact nearest-neighbor containment and noncollapse probes.
   Exact canonical finite axial `Bₙ` coordinates and a measurable extension retaining arbitrary
   axial boundary data on `Bₙᶜ` are constructed. `J(Bₙ)` is defined by literal boundary incidence
   and proved exactly equal to the full box plaquette set. The exact (7.2) density, finite/nonzero
   boundary-dependent normalizer, normalized finite/pushforward laws, and almost-sure `Bₙᶜ`
   retention are constructed. A genuinely-finite measurable bounded-continuous convergence predicate, all-continuous-test coverage bridge, and uninhabited full
   Theorem 7.2 axial contract require a common normalized boundary-independent limit and every free
   `Bₙ` expectation. The exact `ε → 0⁺` filter and spacing-indexed Villain/Wilson families retain
   `Q_{ε²}` or one fixed actual trace representation, with Theorem 8.10 faithfulness as injectivity.
   Definition 8.1 fine edges now have a strengthened exact directed-bond-word interface tied to every
   consecutive certified node, with measurable later-on-the-left coarse restriction. Inhabitation/
   projectivity and Theorems 8.5/8.10 convergence over this transport remain open.
11. Lévy PDF pp. 24–27 / printed pp. 10–13 were visually adjudicated on 2026-07-21 for §1.6,
   Theorem 1.6.1 and Lemma 1.6.3. The pages visibly define the fine-to-coarse holonomy map, state
   surjectivity and exact measure pushforward, and state strict three-graph composition. The Lean
   layer constructs the exact finite-word map/composition, requires literal coarse-path/fine-word
   equality and nonempty edge carriers, records weighted-measure pushforward and coherent observable
   pullback on the unchanged Driver density chain, and derives finite word-family equality in law.
12. Witten's subdivision/sewing formulas are exact representation-theoretic identities, not by
   themselves a countably additive continuum-measure construction.
12. Atiyah–Bott is classical gauge geometry, not a source for a quantum probability measure.
13. Sengupta's orientation-reversing covariance changes to the specified pullback bundle class; it
   must not be simplified to same-bundle invariance.
14. Kluberg-Stern–Zuber's broadest operator-renormalization statements carry dimensional/twist or
   conjectural qualifications; they are corroboration, not an unrestricted theorem.
15. Hollands–Kopper's convergence theorem is not a Yang–Mills convergence theorem.
16. `yang1954.pdf` begins with one page from a preceding article; the Yang–Mills article starts on
   PDF p. 2.

## 4. Concrete progress unlocked by the bundle

The source-acquisition status has changed materially:

- a rigorous 2D continuum/holonomy contract is now source-ready;
- Hodge/action/volume definitions are source-ready, though formal infrastructure remains hard;
- the concrete Poincaré/`SL(2,ℂ)` audit chain is source-ready;
- the BRST/EOM/composite-operator mixing grammar is source-ready;
- the Hall–Wightman extended-tube theorem is source-ready;
- no new source fetch is presently required for those listed tasks unless a more precise edition or
  redistribution-safe public artifact is needed.

The largest remaining literature gap is not among the supplied 33 PDFs: a canonical locally convex
projective tensor product/completion/nuclearity reference suitable for the exact OS functional-
analytic construction should still be selected and retained. OS-I/OS-II specify the target source
spaces but do not replace a modern construction reference for all reusable topology machinery.

## 5. Publication boundary

Several supplied files are purchased books or publisher PDFs. Repository retention records the
private audit corpus. Before public release, each artifact must be classified for redistribution;
where permission is absent, publish hashes, bibliographic identity, extraction-independent page
locators, and acquisition instructions rather than the copyrighted bytes. Removing public bytes
must not erase the private audit record or alter declaration provenance.
