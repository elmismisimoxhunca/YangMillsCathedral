# Yang–Mills acceptance-checker audit bibliography

## Purpose and verification status

This is the literature acquisition and audit plan for the standalone Lean acceptance checker. It
covers both declarations already implemented and the remaining planned work. It is not a claim that
every listed source proves existence of a four-dimensional Yang–Mills theory.

Every DOI-bearing entry below was queried from `https://api.crossref.org/works/<DOI>` on
2026-07-19 and matched against all identity fields supplied by Crossref (title, authors, venue, year,
and volume/pages when present). The retained query snapshot is `docs/AUDIT_DOI_METADATA.tsv`. A DOI match verifies identity, not mathematical interpretation. Before a new source becomes
load-bearing, the project must still retain a lawful source artifact or stable official record,
record its hash, inspect the relevant pages, and add declaration-level locators and hostile probes.

Books, lecture notes, and official problem statements sometimes have no DOI. They are identified by
ISBN, arXiv identifier, publisher page, or canonical institutional URL rather than being assigned an
invented DOI.

The checked-in DOI set and metadata snapshot are verified deterministically with:

```bash
python3 scripts/verify_audit_bibliography.py
```

An explicit network refresh is available with `--online`; it is not a normal build dependency.

## A. Current source-of-record set

These sources already support canonical declarations in `docs/SOURCE_MAP.md`.

| Source | Identifier | Audit role |
|---|---|---|
| Arthur Jaffe and Edward Witten, *Quantum Yang–Mills Theory* | **No DOI**; canonical CMI PDF: <https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf> | Complete Clay endpoint: compact simple `G`, local observables, UV/OPE/stress obligations, Hamiltonian gap and finite supremal mass |
| Daniel S. Freed, *Classical Chern–Simons Theory, Part 1* (1995) | <https://doi.org/10.1006/aima.1995.1039>; arXiv `hep-th/9206021` | Principal bundles, gauge transformations, connections, curvature, Bianchi identity and curvature covariance |
| Brian C. Hall, *An Elementary Introduction to Groups and Representations* (2000) | **No DOI**; arXiv `math-ph/0005032` | Compact Lie-group examples, simple-Lie-algebra terminology and invariant-inner-product averaging |
| Ofer Aharony, Nathan Seiberg and Yuji Tachikawa, *Reading between the lines of four-dimensional gauge theories* (2013) | <https://doi.org/10.1007/JHEP08(2013)115>; arXiv `1305.0318` | Global gauge-group form and the prohibition on silently replacing `G` by its universal cover |
| Konrad Osterwalder and Robert Schrader, *Axioms for Euclidean Green's Functions* (1973) | <https://doi.org/10.1007/BF01645738> | OS-I source spaces, `(E0)`–`(E4)`, reflection operation and original reconstruction program |
| Konrad Osterwalder and Robert Schrader, *Axioms for Euclidean Green's Functions II* (1975) | <https://doi.org/10.1007/BF01608978> | Correcting priority: failure of OS-I Lemma 8.8, strengthened growth and corrected reconstruction theorem |
| A. S. Wightman, *Quantum Field Theory in Terms of Vacuum Expectation Values* (1956) | <https://doi.org/10.1103/PhysRev.101.860> | Vacuum distributions and correlator-level reconstruction semantics |
| Raymond F. Streater and Arthur S. Wightman, *PCT, Spin and Statistics, and All That*, corrected Princeton edition | **No DOI**; ISBN `978-0-691-07062-9` | Mature Wightman axioms, Poincaré cover, joint energy-momentum spectral measure and tube/extended-tube analysis |
| Kenneth G. Wilson, *Non-Lagrangian Models of Current Algebra* (1969) | <https://doi.org/10.1103/PhysRev.179.1499> | Weak OPE organization, singular coefficient distributions and finite-order asymptotics |
| David J. Gross and Frank Wilczek, *Ultraviolet Behavior of Non-Abelian Gauge Theories* (1973) | <https://doi.org/10.1103/PhysRevLett.30.1343> | Negative leading beta function and ultraviolet freedom |
| H. David Politzer, *Reliable Perturbative Results for Strong Interactions?* (1973) | <https://doi.org/10.1103/PhysRevLett.30.1346> | Independent UV/deep-Euclidean analysis and explicit limits on infrared conclusions |
| Daniel N. Blaschke, François Gieres, Méril Reboud and Manfred Schweda, *The energy–momentum tensor(s) in classical gauge theories* (2016) | <https://doi.org/10.1016/j.nuclphysb.2016.07.001>; arXiv `1605.01121` | Classical symmetric gauge-invariant stress tensor, conservation and translation charge formula |
| Kenneth G. Wilson, *Confinement of quarks* (1974) | <https://doi.org/10.1103/PhysRevD.10.2445> | Lattice links, plaquettes, action, Wilson loops and continuum-limit motivation |
| Konrad Osterwalder and Erhard Seiler, *Gauge field theories on a lattice* (1978) | <https://doi.org/10.1016/0003-4916(78)90039-8> | Product-Haar/Gibbs lattice theory and finite-cutoff reflection positivity |

## B. Sources required for remaining canonical work

These are the minimal additions currently needed before the corresponding unfinished interfaces can
be called source-complete.

### B.1 Hodge/action and metric volume

| Source | Identifier | Required use |
|---|---|---|
| Jürgen Jost, *Riemannian Geometry and Geometric Analysis* (2017) | <https://doi.org/10.1007/978-3-319-61860-9> | General oriented-Riemannian definitions and compatibility of the Hodge star, metric volume and integration in the dimension-generic manifold interface |
| Michael Atiyah, Nigel Hitchin and Isadore Singer, *Self-duality in four-dimensional Riemannian geometry* (1978) | <https://doi.org/10.1098/rspa.1978.0143> | Four-dimensional specialization, Hodge decomposition, Yang–Mills action and instanton-sector consistency |

Freed remains sufficient for the pending same-connection Bianchi and covariant-derivative work; no
new paper is required merely to complete those proofs.

### B.2 Poincaré covering and joint spectral measure

| Source | Identifier | Required use |
|---|---|---|
| V. Bargmann, *Irreducible Unitary Representations of the Lorentz Group* (1947) | <https://doi.org/10.2307/1969129> | Independent primary audit of the Lorentz-cover representation background; exact covering topology should be cross-checked against a modern Lie-group treatment |
| Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (2015) | <https://doi.org/10.1007/978-3-319-13467-3> | Modern source for Lie-group topology and the `SL(2,ℂ)`/proper-Lorentz relationship needed by a genuine covering projection |
| D. Hall and A. S. Wightman, *A theorem on invariant analytic functions with applications to relativistic quantum field theory* (1957) | **No DOI found**; *Mat.-Fys. Medd. Dan. Vid. Selsk.* 31, no. 5 | Primary Hall–Wightman extended-tube theorem required by the roadmap's planned derivation of the scalar continuation conclusion |

### B.3 Composite observables, OPE renormalization and mixing

| Source | Identifier | Required use |
|---|---|---|
| Kenneth Wilson and Wolfhart Zimmermann, *Operator product expansions and composite field operators in the general framework of quantum field theory* (1972) | <https://doi.org/10.1007/BF01878448> | Bridge between OPE terms and renormalized composite fields |
| Wolfhart Zimmermann, *Composite operators in the perturbation theory of renormalizable interactions* (1973) | <https://doi.org/10.1016/0003-4916(73)90429-6> | Subtractions, finite operator bases and perturbative composite-operator semantics |
| Satish Joglekar and Benjamin Lee, *General theory of renormalization of gauge invariant operators* (1976) | <https://doi.org/10.1016/0003-4916(76)90225-6> | Central source for gauge-invariant operator mixing with BRST-exact and equation-of-motion sectors; prevents a fictitious injective quantization map |
| H. Kluberg-Stern and J.-B. Zuber, *Renormalization of non-Abelian gauge theories in a background-field gauge. II. Gauge-invariant operators* (1975) | <https://doi.org/10.1103/PhysRevD.12.3159> | Independent primary check of non-Abelian gauge-invariant composite-operator renormalization |
| Glenn Barnich, Friedemann Brandt and Marc Henneaux, *Local BRST cohomology in gauge theories* (2000) | <https://doi.org/10.1016/S0370-1573(00)00049-1> | Authoritative review for the typed local grammar built from curvature and covariant derivatives and for distinctions among strict invariance, BRST classes, total derivatives and on-shell equivalence |
| Kurt Symanzik, *Small distance behaviour in field theory and power counting* (1970) | <https://doi.org/10.1007/BF01649434> | Required short-distance/power-counting audit for the roadmap's planned controlled perturbative remainder layer |

### B.4 Beta-function normalization and trace anomaly

| Source | Identifier | Required use |
|---|---|---|
| John Collins, Anthony Duncan and Satish Joglekar, *Trace and dilatation anomalies in gauge theories* (1977) | <https://doi.org/10.1103/PhysRevD.16.438> | Required source for the renormalized gauge-theory trace identity tying the same beta function to the same renormalized `F²` mixing class, with BRST/EOM/contact-term qualifications |

Gross–Wilczek and Politzer remain the primary sources for the leading asymptotic-freedom result.
The Lean bridge must still define `C_A` relative to the selected invariant pairing and coupling
convention; Caswell is retained below as an independent optional cross-check, not a replacement.

### B.5 Rigorous two-dimensional consistency evidence

| Source | Identifier | Required use |
|---|---|---|
| Bruce Driver, *YM2: Continuum expectations, lattice convergence, and lassos* (1989) | <https://doi.org/10.1007/BF01218586> | Rigorous two-dimensional continuum expectations and lattice convergence; a natural primary anchor for the 2D consistency contract |
| Leonard Gross, Christopher King and Ambar Sengupta, *Two dimensional Yang-Mills theory via stochastic differential equations* (1989) | <https://doi.org/10.1016/0003-4916(89)90032-8> | Independent stochastic construction of the 2D Yang–Mills measure/holonomy theory |
| Ambar Sengupta, *Gauge theory on compact surfaces* (1997) | <https://doi.org/10.1090/memo/0600> | Compact-surface measure, gauge invariance and holonomy formulas |

A 2D source may inhabit only a source-specific 2D consistency interface. It cannot inhabit the 4D
Clay contract or automatically supply scalar OS-II/Wightman fields, a stress tensor, OPE, or the
same-PVM Clay mass gap.

## C. Conditional cross-check sources

These are useful only if the named optional layer is introduced; they are not current completion
blockers.

| Source | Identifier | Trigger for use |
|---|---|---|
| C. N. Yang and R. L. Mills, *Conservation of Isotopic Spin and Isotopic Gauge Invariance* (1954) | <https://doi.org/10.1103/PhysRev.96.191> | Historical cross-check for non-Abelian gauge fields; modern bundle semantics continue to use Freed |
| Dale Husemoller, *Fibre Bundles*, 3rd ed. (1994) | <https://doi.org/10.1007/978-1-4757-2261-1> | Add only if global topological sectors are introduced; guards against unexplained nontrivial bundles on bare contractible `ℝ⁴` |
| Warren Ambrose, *Spectral resolution of groups of unitary operators* (1944) | <https://doi.org/10.1215/S0012-7094-44-01151-8> | Original SNAG cross-check; the existing PVM layer is already canonically sourced to visually checked Streater–Wightman |
| William Caswell, *Asymptotic Behavior of Non-Abelian Gauge Theories to Two-Loop Order* (1974) | <https://doi.org/10.1103/PhysRevLett.33.244> | Independent group/coefficient cross-check if the checker extends beyond the one-loop bridge sourced by Gross–Wilczek and Politzer |
| Thierry Lévy, *Yang-Mills measure on compact surfaces* (2003) | <https://doi.org/10.1090/memo/0790> | Add if the 2D model needs a stronger gluing/Markov/projective-limit treatment |
| Edward Witten, *On quantum gauge theories in two dimensions* (1991) | <https://doi.org/10.1007/BF02100009> | Physical/geometric cross-check for exact 2D formulas; not the sole rigorous construction source |
| Michael Atiyah and Raoul Bott, *The Yang-Mills equations over Riemann surfaces* (1983) | <https://doi.org/10.1098/rsta.1983.0017> | Add if the 2D contract includes moduli-space or symplectic geometry |
| Isadore Singer, *Some remarks on the Gribov ambiguity* (1978) | <https://doi.org/10.1007/BF01609471> | Required only if a global gauge-fixing slice or orbit-space trivialization is claimed |
| Stefan Hollands, *Renormalized quantum Yang–Mills fields in curved spacetime* (2008) | <https://doi.org/10.1142/S0129055X08003420> | Modern perturbative audit if curved-spacetime/local-covariance or BRST-renormalized field infrastructure is added |
| Stefan Hollands and Christoph Kopper, *The Operator Product Expansion Converges in Perturbative Field Theory* (2012) | <https://doi.org/10.1007/s00220-012-1457-4> | Add only if the checker strengthens supplied asymptotics to a perturbative OPE convergence theorem |
| Curtis Callan, *Broken Scale Invariance in Scalar Field Theory* (1970) | <https://doi.org/10.1103/PhysRevD.2.1541> | General RG/scale-Ward background; not a Yang–Mills trace-anomaly source by itself |

## D. Coverage and stopping rules

| Remaining checker work | Sufficient audit chain |
|---|---|
| Adjoint-valued forms, covariant exterior derivative and Bianchi | Freed |
| General Hodge star and metric-volume interface; four-dimensional action bridge | Jost for the dimension-generic geometry + Clay and Atiyah–Hitchin–Singer for the 4D specialization |
| Exact OS carriers, topology, `(E2)` and corrected reconstruction | OS-I + OS-II |
| Genuine `SL(2,ℂ)` cover | Streater–Wightman + Bargmann + Hall 2015 |
| Joint translation PVM and Hamiltonian gap semantics | Streater–Wightman + Clay; Ambrose is an optional original-theorem cross-check |
| Extended-tube derivation | Hall–Wightman + Streater–Wightman |
| Curvature-polynomial grammar and quantum mixing | Clay + Freed + Joglekar–Lee + Kluberg-Stern–Zuber + Barnich–Brandt–Henneaux |
| OPE/composite-field bridge and controlled short-distance remainder | Wilson 1969 + Wilson–Zimmermann + Zimmermann + Symanzik |
| Group-normalized beta coefficient | Gross–Wilczek + Politzer plus a proved invariant-pairing/coupling bridge; Caswell is an optional cross-check |
| Stress trace anomaly | Blaschke et al. for classical tensor + Collins–Duncan–Joglekar for the quantum trace identity |
| Rigorous 2D consistency contract | Driver + Gross–King–Sengupta; Sengupta for compact surfaces |
| Positive classical curvature examples and disconnected-curvature probes | Hall for compact-group/invariant-pairing input + Freed for exact connection/curvature semantics + Atiyah–Hitchin–Singer for nontrivial 4D geometric examples; this does not construct the repository's full gauge-group certificate |
| Lattice renormalization and continuum OS/Wightman bridge semantics | Wilson 1974 and Osterwalder–Seiler for the regulator + OS-I/OS-II for the independent target; no theorem of 4D continuum construction is claimed |
| 3D uninhabited project contract | Existing general sources suffice; no positive 3D continuum model may be claimed without a new construction source |
| 4D final acceptance proposition | Clay plus every explicit bridge above; no inhabitant is asserted |
| Rigorous 4D lattice-to-continuum construction | No listed source supplies this open mathematics; it must remain an uninhabited acceptance obligation |

Do not keep adding literature merely for volume. A new source is warranted only when a declaration
makes a mathematical or physical claim not covered by this matrix, when a correcting source changes
an older theorem, or when an exact convention cannot be audited from the retained source.

## E. DOI correction log

Online verification caught several plausible but incorrect identifiers. They must not enter source
records:

- Freed is `10.1006/aima.1995.1039`, **not** `10.1006/aima.1995.1025`.
- Ambrose is `10.1215/S0012-7094-44-01151-8`, **not** an `...01149-3` variant.
- Driver is `10.1007/BF01218586`; `10.1007/BF01218585` is an unrelated wave-equation paper.
- Gross–King–Sengupta is `10.1016/0003-4916(89)90032-8`, **not** `...90032-6`.
- No working DOI was found for the 1957 Hall–Wightman paper; `10.1073/pnas.43.3.254`
  does not resolve and must not be cited for it.
