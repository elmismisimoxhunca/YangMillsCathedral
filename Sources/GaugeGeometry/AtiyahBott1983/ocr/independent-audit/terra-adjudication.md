# OCR adjudication — Atiyah–Bott (1983), pp. 548, 551–552

Independent report and the supplied page images were checked against the calibrated Mathpix drafts. Harmless spacing and TeX-font normalizations are not counted as discrepancies.

## Review

### p548 — `/root/mathpix-extractor/output/atiyah1983/normalized-calibrated/p548.md`
- **Printed-page/annotation audit:** metadata `printed_page: 548` (line 6) matches the printed **548**. Low-confidence lines 0.84 and 0.87 (lines 69, 71) are exact, including the line-break hyphen in *normal-ized*. Line 0.93 (line 91) has the right two assertions: \(\theta_A(Z)=1\), \(i(Z)\theta_A=1\), and \(\mathscr L(Z)\theta_A=0\). The source prints these separately as (3.5) and (3.6); the draft collapses them into one `gathered` display. The annotation copy of 0.93 is itself truncated/unclosed (line 107).
- **Exact substantive agreements:** the Lie-algebra extension (3.4), horizontal-lift curvature formula, \(F(A)\in\Omega^2(M;\operatorname{ad}(P))\), \(L(A)=\lVert F(A)\rVert^2\), circle-bundle normalization, and \(d\theta_A=-\pi^*F(A)\) agree with the independent read and image.
- **Discrepancy:** line 65 renders the norm operator as malformed `\left\| \| \right.` rather than the printed empty norm \(\lVert\ \rVert\). This is a TeX/text defect, not a change to the stated norm.
- **Source-use decision:** **safe after the two display-labels and norm notation are normalized**; raw Mathpix text should not be copied verbatim for those items.

### p551 — `/root/mathpix-extractor/output/atiyah1983/normalized-calibrated/p551.md`
- **Printed-page/annotation audit:** metadata `printed_page: 551` (line 6) matches the printed **551**. Low-confidence results: 0.66 (line 31) **incorrect**; it should be \(\nabla_X^A s\), not `\nabla_X^{\frac{A}{X}}s`. 0.94 (line 35) **correct**. 0.79 (line 39) **incorrect**; the source is \(\nabla^A_{\widetilde X}s=d_As(X)=[\widetilde X,s]\), while the draft drops the tilde on the subscript. 0.89 (line 61) **correct**. 0.74 (line 91) **correct**. Annotation excerpts for 0.94 and 0.74 are truncated (lines 98, 101), so they are not lossless annotation records.
- **Exact substantive agreements:** (4.2), the induced-bundle compatibility statement, (4.3)–(4.4), Lemma 4.5's curvature formula \(F(A_t)=F(A)+td_A\eta+\tfrac12t^2[\eta,\eta]\), \(\omega_t=\omega-t\eta\circ\pi\), and the definition of \([\alpha,\beta](X,Y)\) agree.
- **Discrepancies:**
  1. Line 25 reads \(\tilde s(pg)=p(g^{-1})\tilde s(p)\); the source has \(\tilde s(pg)=\rho(g^{-1})\tilde s(p)\). The representation \(\rho\) was misread as \(p\).
  2. Line 31 has the malformed covariant-derivative superscript noted above.
  3. Line 39 loses \(\widetilde X\) in the derivative subscript.
  4. Line 81 has \(\widetilde X_t=X_t+t\eta(X)\); the source has \(\widetilde X_t=\widetilde X+t\eta(X)\).
  5. In the first equality of line 89, the source has the two linear terms \(t[\widetilde X,\eta(Y)]\) and \(t[\eta(X),\widetilde Y]\); Mathpix omits both factors \(t\). Its final quadratic bracket is also malformed (`[\eta(X,\eta(Y)]`) instead of \([\eta(X),\eta(Y)]\). (The second equality on that line has the correct factors and bracket.)
  6. The separate printed displays (4.3) and (4.4) are merged into one aligned display (line 67); content is preserved but equation-label/display association is flattened.
- **Source-use decision:** **not safe** as a page-level source. It contains unflagged errors in the associated-bundle equivariance formula and the curvature-variation proof, plus two incorrect low-confidence mathematical lines.

### p552 — `/root/mathpix-extractor/output/atiyah1983/normalized-calibrated/p552.md`
- **Printed-page/annotation audit:** metadata `printed_page: 552` (line 6) matches the printed **552**. The sole low-confidence annotation, equation number (4.9) (lines 51, 111), is correct and complete.
- **Exact substantive agreements:** Proposition (4.6); (4.7) including its factor \(2t\), the \(t^2\) terms and \((F,[\eta,\eta])\); (4.8); the sign/exponent in \(d_A^*=(-1)^{m+mp+1}*d_A*\) on \(\Omega^p\); the compact-support adjoint proof and \(*^{-1}=(-1)^{(p-1)(m-p+1)}*\); the Bianchi/adjoint equations; Proposition (4.10); and (4.11), including \((-1)^{m+1}\), all agree with the independent read and image.
- **Discrepancies:** none substantive found. `\mathscr A` versus the printed calligraphic glyph and `\mathrm p` in line 71 are presentational TeX normalizations only.
- **Source-use decision:** **safe** for source use.

## Acceptance report
```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Wrote only the required adjudication and compared every supplied calibrated page to the independent report and page image, including all low-confidence annotations and printed-page fields."
    }
  ],
  "changedFiles": [
    "/tmp/mathpix-independent/atiyah1983/terra-adjudication.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git -C /root/projects/lean-yangmills-adaly/YangMillsDefinition diff --cached --name-only; git -C /root/projects/lean-yangmills-adaly/YangMillsDefinition status --short",
      "result": "passed",
      "summary": "No staged or working-tree files reported in the implementation repository."
    }
  ],
  "validationOutput": [
    "Visually checked p548.png, p551.png, and p552.png against the calibrated drafts.",
    "The supplied root plan.md and progress.md paths were absent (ENOENT); the independent report records the same condition."
  ],
  "residualRisks": [
    "p551 is not safe until the listed OCR defects are corrected and independently rechecked.",
    "The PDF-page metadata was not independently verifiable from the supplied PNGs; printed-page values were verified."
  ],
  "noStagedFiles": true,
  "diffSummary": "Created the required external OCR adjudication; no repository source changed.",
  "reviewFindings": [
    "blocker: normalized-calibrated/p551.md:25,31,39,81,89 - representation/operator/lift and curvature-expansion OCR errors.",
    "no blocker: p548 and p552 are source-safe with the stated p548 normalization."
  ],
  "manualNotes": "Annotation excerpts on p548 and p551 are truncated even when their underlying verbatim line is adequate."
}
```
