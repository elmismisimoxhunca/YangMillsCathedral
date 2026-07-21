# Atiyah 1978 Mathpix adjudication

Basis: independent visual transcription in `terra-independent.md` and direct page-image check of `p427.png`, `p430.png`, and `p451.png`. The requested repository-root `plan.md` and `progress.md` do not exist (both returned ENOENT).

## Review

### Printed-page and calibration audit
All three front-matter claims match the printed folio visible in the supplied images: `p427.md:6` = **427**, `p430.md:6` = **430**, and `p451.md:6` = **451**. The `pdf_page` values (4, 7, 28) are PDF indices, not printed pages. Each file is correctly labelled a Mathpix machine draft/non-citable pending adjudication (`p427.md:8-12,107`; `p430.md:8-12,114`; `p451.md:8-12,98`).

### Page 427
- **Correct:** Exact substantive agreement for the independently transcribed Hodge passage: the definition `\alpha\wedge *\beta=(\alpha,\beta)\omega`, middle-degree map and `*^2=(-1)^l`, conformal scaling, and the `l=2` splitting `\Lambda^2=\Lambda^2_+\oplus\Lambda^2_-` with the \(\pm1\)-eigenspace names (`p427.md:25-57`). Direct image check also confirms the remainder: the `l=1` complex-structure sentence and the curvature-operator/block/Weyl decomposition (`p427.md:47-97`).
- **Low-confidence lines:** All four annotations are correctly read: `p=l`, star-square, and conformal invariance (0.95; lines 39/103); eigenspaces/self-dual (0.85; 55/104); anti-self-dual continuation (0.92; 57/105); and the curvature-tensor relation (0.78; 59/106).
- **Note:** The independent report did not itself include the `l=1` or curvature-decomposition remainder; this is a coverage limitation of that report, not an OCR discrepancy. The image confirms it.
- **Source-use decision:** **Yes.** Safe for source use as adjudicated text; do not cite the download banner or machine-draft metadata as paper content.

### Page 430
- **Correct:** The principal/vector-bundle exposition agrees: curvature `d\omega+\tfrac12[\omega,\omega]`, descent to the adjoint bundle, `D_1`, its Leibniz formula, associated bundle/local frame construction, matrix formula `\nabla e_i=\sum_j\omega_{ij}\otimes e_j`, physics names, and the two visible gauge-transformation conditions (`p430.md:41-99`). The preceding almost-complex/self-dual-object passage also matches the image (`p430.md:23-37`).
- **Discrepancies:**
  1. `p430.md:49` reads plain `g` for the Lie algebra; the printed/independent text is `\mathfrak g`. The same loss occurs in `p430.md:89` (`A^2(g)` must be `A^2(\mathfrak g)`).
  2. `p430.md:61` has `A^{\circ}(E)`; the printed operator domain is **`A^0(E)`**. This is a load-bearing degree/index error.
  3. `p430.md:77` breaks `A^2(\operatorname{End}E)` across math delimiters as `A^{2}$ (End $E$ )`; the printed and independent reading is **`D_1\nabla\in A^2(\operatorname{End}E)`**.
  4. `p430.md:97` omits the separator after `f(p)`: printed text is `f(gp)=gf(p),\ g\in G,\ p\in P`; the draft's run-on form is not verbatim.
- **Low-confidence lines:** Correct: 0.78 (skew-adjoint `I`), 0.90/0.87 (self-/anti-self-dual classes), 0.67 (principal bundle), 0.72 (descent/adjoint bundle), 0.54 (`\nabla`), 0.92 (associated bundle), and both 0.86 lines (matrix and preserved \(G\)-structure) (`p430.md:103-113`). Incorrect: 0.26 loses `\mathfrak g`; the 0.90 `D_1\nabla` line has the malformed `A^2(\operatorname{End}E)` grouping.
- **Source-use decision:** **No for the raw machine draft.** It becomes safe only with all four corrections above; the independent report also correctly warns that no self-dual-connection definition or continuation of gauge equivalence is visible on this page.

### Page 451
- **Correct:** The projection formula, the norm/\(\rho\) formulas, the flat connection, the Clifford identity, (7.1) including its minus one-half factor, `\alpha=-\tfrac12d\log\rho`, `\Omega=d\omega+\tfrac12[\omega,\omega]`, the scalar condition `d^*\alpha+2(\alpha,\alpha)=0`, and its reduction to `\Delta\rho=0` agree (`p451.md:23-75,83-89`).
- **Discrepancies:**
  1. The summation index in the connection matrix is corrupted at `p451.md:49`: **`\sum_{i=1}^k`**, not `\sum_{i-1}^k`.
  2. The natural-map formula at `p451.md:67` has a Clifford dot: `\sum(e_j\cdot\alpha)_-\otimes e_j`. The printed/independent formula is **`\sum(e_j,\alpha)_-\otimes e_j`** (inner-product comma), a different operator.
  3. `p451.md:77` changes both bundles in the excluded component. Printed: **`\Lambda_-^2\otimes\Lambda^2\simeq1\oplus\Lambda_+^2\oplus S^4V_-`**. Draft: `\Lambda_-^2\otimes\Lambda_-^2\cong1\oplus\Lambda_-^2\oplus S^4V_-`.
  4. `p451.md:81` changes the skew-map target from printed **`\Lambda^2`** to `\Lambda_-^2`.
- **Low-confidence lines:** Correct: 0.78 projection formula (`p451.md:43/93`), 0.80 unitary basis (the bold styling in `L_{\mathbf0}` is non-substantive; 45/94), 0.84 equation (7.1) (57/95), 0.89 definition of \(\alpha\) (63/96), and 0.53 `\Lambda_-^2\cong\mathfrak{su}(2)`/curvature formula (69/97). The three serious errors above are in *unflagged* lines 49, 67, 77, and 81; calibration therefore failed to highlight the load-bearing bundle/operator/index errors.
- **Source-use decision:** **No for the raw machine draft.** Use the independent/adjudicated readings for the four corrections, especially the index, inner product, and \(\Lambda^2\) versus \(\Lambda_-^2\)/\(\Lambda_+^2\) distinctions.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Wrote the requested three-page OCR adjudication only to /tmp/mathpix-independent/atiyah1978/terra-adjudication.md; it records agreements, every verified substantive discrepancy, low-confidence-line outcomes, source-use decisions, and folio/annotation audit."
    }
  ],
  "changedFiles": [
    "/tmp/mathpix-independent/atiyah1978/terra-adjudication.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git -C YangMillsDefinition status --short && git -C YangMillsDefinition diff --check && git -C YangMillsDefinition diff --cached --check && git -C YangMillsDefinition diff --cached --name-only",
      "result": "passed",
      "summary": "No output: canonical repository has no unstaged/staged changes, whitespace errors, or staged files."
    },
    {
      "command": "nl -ba .../p427.md; nl -ba .../p430.md; nl -ba .../p451.md",
      "result": "passed",
      "summary": "Obtained line-numbered evidence for all calibrated draft and annotation findings."
    }
  ],
  "validationOutput": [
    "Direct visual audit confirmed printed folios 427, 430, and 451.",
    "p427 has no substantive OCR discrepancy; p430 has degree/Lie-algebra/grouping/punctuation errors; p451 has index, operator, and bundle-target errors."
  ],
  "residualRisks": [
    "The root paths plan.md and progress.md specified by the task do not exist (ENOENT).",
    "Raw p430 and p451 Mathpix drafts remain unsafe until the listed corrections are applied."
  ],
  "noStagedFiles": true,
  "diffSummary": "Created the required external markdown adjudication; repository files were not modified.",
  "reviewFindings": [
    "blocker: /root/mathpix-extractor/output/atiyah1978/normalized-calibrated/p451.md:49,67,77,81 - incorrect summation index, inner-product operator, and self-duality bundle targets.",
    "blocker: /root/mathpix-extractor/output/atiyah1978/normalized-calibrated/p430.md:61 - A^0(E) was OCRed as A^\\circ(E)."
  ],
  "manualNotes": "The independent report's limited p427 coverage omits the l=1 and curvature-decomposition remainder, and its p430 warning about page-boundary omissions is retained; direct image audit confirmed the relevant visible text."
}
```
