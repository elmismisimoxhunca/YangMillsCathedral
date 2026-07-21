# Independent visual transcription

Method: read directly from the three specified page images only; no Mathpix/OCR output was consulted. Mathematical glyphs below were visually legible; no `[?]` markers are required.

## `p427.png`

**Printed page:** 427 — visually unambiguous.

> Let \(X\) be an oriented Riemannian manifold of even dimension \(2l\), and let \(\Lambda^p\) denote the bundle of exterior \(p\)-forms with \(A^p=\Gamma(\Lambda^p)\) its space of smooth sections. The Hodge star operator \(*:\Lambda^p\to\Lambda^{2l-p}\) is defined by
> \[
> \alpha\wedge *\beta=(\alpha,\beta)\omega\in\Lambda^{2l}
> \]
> where \(\alpha,\beta\in\Lambda^p\), \((\alpha,\beta)\) is the induced inner product on \(p\)-forms and \(\omega\) is the volume form.
>
> Of particular interest is the star operator on forms in the middle dimension \(p=l\), where \(*:\Lambda^l\to\Lambda^l\) satisfies \(*^2=(-1)^l\). On \(l\)-forms \(*\) is conformally invariant, for if we change the metric by multiplying by a scalar \(\lambda\), the inner product on tangent vectors is multiplied by \(\lambda\) and on \(l\)-forms by \(\lambda^{-l}\). On the other hand the volume form is multiplied by \(\lambda^l\) and \((\alpha,\beta)\omega=\alpha\wedge *\beta\) remains the same.
>
> We are interested in the case \(l=2\), i.e. when \(X\) is a four-dimensional manifold. In this instance \(*^2=+1\) and the bundle \(\Lambda^2\) splits into a direct sum,
> \[
> \Lambda^2=\Lambda^2_+\oplus\Lambda^2_-,
> \]
> where \(\Lambda^2_\pm\) are the \(\pm1\) eigenspaces of \(*\). We call them the bundles of *self-dual* and *anti-self-dual* 2-forms respectively.

## `p430.png`

**Printed page:** 430 — visually unambiguous.

> Connections can always be viewed in two ways: as defined on principal bundles, or vector bundles. We shall use both methods, so we begin by reviewing the relation between them.
>
> On a *principal \(G\)-bundle* \(P\) over \(X\), a connection is defined by a 1-form \(\omega\) with values in the Lie algebra \(\mathfrak g\) of \(G\), and its curvature \(\Omega\) is the \(\mathfrak g\)-valued 2-form
> \[
> d\omega+\tfrac12[\omega,\omega],
> \]
> which descends to \(X\) as a section of \(\mathfrak g\otimes\Lambda^2\) where \(\mathfrak g\) now denotes the vector bundle associated to \(P\) by the adjoint representation.
>
> On a *vector bundle* \(E\) over \(X\), a connection is defined by its covariant derivative \(\nabla\), which is a first order linear differential operator
> \[
> \nabla:A^0(E)\longrightarrow A^1(E),
> \]
> where \(A^p(E)=\Gamma(E\otimes\Lambda^p)\) is the space of smooth sections of \(E\otimes\Lambda^p\). The covariant derivative has a natural extension
> \[
> D_1:A^1(E)\longrightarrow A^2(E), \tag{2.1}
> \]
> defined by
> \[
> D_1(e\otimes\alpha)=\nabla e\wedge\alpha+e\otimes d\alpha,
> \]
> where \(e\in A^0(E)\) and \(\alpha\in A^1\). The curvature \(\Omega\) is then defined as the composition \(D_1\nabla\in A^2(\operatorname{End}E)\). The relation is easy to describe. A representation of \(G\) on a vector space \(E\) defines an associated vector bundle \(P\times_G E\) and a local section of \(P\) a distinguished local basis \(\{e_i\}\) of \(E\). Pulling back \(\omega\) via the section and applying the representation we get a matrix of 1-forms \(\omega_{ij}\) and define \(\nabla e_i=\sum_j\omega_{ij}\otimes e_j\). Conversely if \(E\) has a \(G\)-structure preserved by \(\nabla\), then this defines \(\omega\) on the principal bundle of \(G\)-frames.
>
> For the physicist the curvature \(\Omega\in A^2(\mathfrak g)\) is called the *gauge field*, and the connection form \(\omega\) the *gauge potential*. The concept of equivalence of two connections which is appropriate here is that of gauge equivalence.
>
> *Definition.* A *gauge transformation* on a principal \(G\)-bundle \(P\) is a diffeomorphism \(f:P\to P\) such that (1) \(f(gp)=gf(p)\), \(g\in G,\ p\in P\), (2) \(f\) preserves each fibre, i.e. acts trivially on the base space \(X\).

The image calls the fields “self-dual Yang–Mills fields or *self-dual connections* which we consider next,” but it contains **no definition** of a self-dual connection. Likewise, the displayed gauge-transformation definition ends at the page boundary; no subsequent definition of equivalence is visible in this image.

## `p451.png`

**Printed page:** 451 — visually unambiguous.

> Hence the connection matrix relative to this basis is
> \[
> \omega=-\sum_{i=1}^k(x_i^{-1}/\rho)\nabla(x_i^{-1}).
> \]
>
> However using the fact that \(x^{-1}=-x/r^2\) in Clifford multiplication we see that
> \[
> -x^{-1}\cdot\nabla(x^{-1})\cdot\phi=\sum e_j\cdot(x/r^4)\otimes e_j
> \]
> and since \(d(1/r^2)=-2x/r^4\), then
> \[
> \omega=-\tfrac12\sum e_j\cdot d(\log\rho)\otimes e_j. \tag{7.1}
> \]
> where \(\rho=1+\sum m_i^2/r_i^2\). \(\omega\) is thus locally given as the image of a 1-form \(\alpha=-\tfrac12d(\log\rho)\) under the natural map
> \[
> \Lambda^1\longrightarrow\Lambda^2_-\otimes\Lambda^1,
> \]
> \[
> \alpha\longmapsto\sum(e_j,\alpha)_-\otimes e_j,
> \]
> where \(\Lambda^2_-\) is identified with the Lie algebra of \(SU(2)\). The curvature \(\Omega=d\omega+\tfrac12[\omega,\omega]\) is then in the image of natural maps
> \[
> \Lambda^1\otimes\Lambda^1\longrightarrow\Lambda^2_-\otimes\Lambda^2
> \]
> both from the derivative term \(\nabla\alpha\) and the quadratic term \(\alpha\otimes\alpha\). For \(E\) to be *self-dual*, we require the component in \(\Lambda^2_-\otimes\Lambda^2\simeq1\oplus\Lambda^2_+\oplus S^4V_-\) to be zero. But there are only two such natural maps: the inner product \(\Lambda^1\otimes\Lambda^1\to1\), and the skew part \(\Lambda^1\otimes\Lambda^1\to\Lambda^2\). For the derivative term, since \(d\alpha=0\) the skew-part vanishes and since \(\alpha\otimes\alpha\) is symmetric, it vanishes on this too. The remaining scalar condition is \(d*\alpha+2(\alpha,\alpha)=0\) which for \(\alpha=-\tfrac12d(\log\rho)\) reduces to \(\Delta\rho=0\) which is satisfied for \(\rho=1+\sum m_i^2/r_i^2\). Hence these connections are all *self-dual*.

## Review
- Correct: Each requested image visibly bears its printed page number (427, 430, and 451), and the requested Hodge, connection/curvature, gauge-transformation, and curvature passages are transcribed above from those images.
- Note (medium): `p430.png` ends immediately after the two conditions defining a gauge transformation. Its self-dual-connection definition and any continuation defining gauge equivalence are not visible; they cannot be transcribed from this page image without inventing text.
- Note (low): `p451.png` uses the symbol \(\nabla\alpha\) for the derivative term while its displayed curvature formula is \(\Omega=d\omega+\tfrac12[\omega,\omega]\); this is transcribed as printed.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete, image-only transcription and review findings are recorded in /tmp/mathpix-independent/atiyah1978/terra-independent.md, with source image paths and medium/low severity notes."
    }
  ],
  "changedFiles": [
    "/tmp/mathpix-independent/atiyah1978/terra-independent.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [],
  "validationOutput": [
    "Visually inspected p427.png, p430.png, and p451.png directly; printed page numbers are unambiguous."
  ],
  "residualRisks": [
    "The requested self-dual-connection definition and a completed definition of gauge equivalence are not visible in p430.png; this independent image-only audit does not supply text from another page."
  ],
  "noStagedFiles": false,
  "diffSummary": "Created the required independent visual-transcription report outside the repository.",
  "reviewFindings": [
    "medium: /tmp/mathpix-independent/atiyah1978/p430.png - the relevant definitions requested by the task are not fully present before the visible page boundary.",
    "low: /tmp/mathpix-independent/atiyah1978/p451.png - curvature is explicitly printed as Ω = dω + 1/2[ω,ω], while the following prose calls its derivative contribution ∇α."
  ],
  "manualNotes": "No Mathpix output, OCR, plan.md, or progress.md was inspected, in order to preserve the user-mandated independent image-only transcription."
}
```