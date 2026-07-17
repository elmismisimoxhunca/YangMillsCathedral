# Gauge global-form source pin

## Identity

- Ofer Aharony, Nathan Seiberg, and Yuji Tachikawa,
  **Reading between the lines of four-dimensional gauge theories**.
- arXiv:1305.0318v5; JHEP 08 (2013) 115.
- DOI: <https://doi.org/10.1007/JHEP08(2013)115>.
- Versioned artifact URL: <https://arxiv.org/pdf/1305.0318v5>.
- Retrieved at the UTC time in `FETCH_TIMESTAMP.txt` with
  `curl --proto '=https' --tlsv1.2 -fL --retry 3`.
- Text produced by `pdftotext -layout` 25.03.0.

## Load-bearing locators

Printed p. 1, Introduction; extracted lines 44–65:

- analysis starts by choosing a Lie algebra `g` and a gauge group `G`;
- local correlators on `ℝ⁴` depend only on the Lie algebra, while the global structure affects line
  operators, phases, compactifications, and vacuum data.

Printed p. 2, §1.1; extracted lines 84–119:

- the paper explicitly restricts its discussion to connected gauge groups;
- if `G̃` is the universal cover and `C` its center, the gauge group is a quotient
  `G = G̃/H` for `H ≤ C`;
- the choice of `G` affects representations, Wilson lines, bundle sectors, instanton data, and
  discrete parameters, even without matter fields.

## Formalization decision

This source establishes that the Lie algebra and the global gauge group are not interchangeable and
that replacing every group by its simply connected cover loses physical specification. The project
will therefore keep the group carrier/global form explicit and will not reduce the Clay quantifier
to `SU(N)` or simply connected groups.

Connectedness remains an explicit **project convention** for expanding Clay's terse “compact simple
gauge group” phrase. This paper studies connected groups; it does not prove that Clay's wording
logically excludes every disconnected extension. The convention and this limitation must remain in
the source map.

The paper concerns global structure and line operators, including supersymmetric examples. It is
not evidence for existence or a mass gap and is never used as such.
