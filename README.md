# The uncomputable price of precision

Seth Douglas and Nidhal Mghirbi. Version 3.0.0, October 2026. DOI: [10.5281/zenodo.23736188](https://doi.org/10.5281/zenodo.23736188).

Concept DOI (latest version): [10.5281/zenodo.23701733](https://doi.org/10.5281/zenodo.23701733). Released versions: [v2.0.0](https://doi.org/10.5281/zenodo.23717986), [v1.0.0, A nonlocal game whose dimension exponent is uncomputable](https://doi.org/10.5281/zenodo.23701734).

## Abstract

Which numbers can be the entanglement price of perfection for one fixed finite game? The positive dimension exponents of finite rational Boolean constraint-system games of quantum value one are exactly the positive $\Delta^0_2$ reals. For every such $\alpha$ we construct one game, with no finite-dimensional perfect strategy, whose least local dimension satisfies $\log_2D_G(\varepsilon)=\alpha\log_2(1/\varepsilon)+o(\log(1/\varepsilon))$. The infimum one-way distillable entanglement of the original mixed strategy state has the same coefficient. This is a realization theorem for usable entanglement; its full spectrum remains open. A finite stop-or-continue program combines finite perfect witnesses from MIP*=RE with a scalar tail verifier for an arbitrary computable convergent rational sequence. Per-gate data are loaded once and held fixed while checked. Matrix-approximable traces give the lower bound; finite threshold histories with sublinear logarithmic witness overhead give matching models. The left-c.e. construction, exact-trace obstruction and non-left-c.e. example of version 2.0.0 become steps toward the classification. In the reset model of the companion heat paper, local-reset heat has coefficient $2\alpha$, while joint-reset heat stays bounded: the order of communication and reset changes the asymptotic cost of one device. With recovery before reset, the critical quantum return rate is $\alpha$ in the companion block model. Every positive $\Delta^0_2$ local-heat coefficient is thus realized; the full heat spectrum and the computability of the finite-precision heat function remain open. The version-1.0.0 halting-degree game and its proofs are retained. Meyerovitch's classification of entropy dimensions is the precedent in form; here the classified exponent is a nonlocal-game dimension cost.

## What version 3 proves

- The positive dimension exponents of finite rational BCS games of quantum value one are exactly the positive Delta^0_2 reals.
- Every positive Delta^0_2 real also occurs as the logarithmic one-way distillable-entanglement coefficient of the **original mixed state**. The full usable spectrum remains open.
- A stop-or-continue program with per-gate loaded data gives a matrix-approximable flag minimum of `1-theta` for every computable convergent rational approximation to theta, with matched finite models.
- Local-reset heat has twice the matched coefficient; joint-reset heat of the same device stays bounded. The claim concerns limiting coefficients, not computability of a finite-precision heat function.

The approximable projection minima are classified separately as the reals in [0,1] left-c.e. relative to the halting problem, with an explicit obstruction to a matched witness budget. In the companion block model, the critical quantum-recovery rate equals the dimension coefficient; it is undecidable uniformly even under a two-rational promise. The full local-heat spectrum has an arithmetic upper bound and remains open. Real and complex dimension exponents agree, and positive reweighting preserves the exponents.

The v1 halting-degree game, proofs and checks are retained byte-for-byte in the protected core. The v2 reader, extraction, exact-trace barrier and non-left-c.e. escape remain steps toward the classification. Numbered open problems cover zero exponents, the full usable spectrum, linear systems and groups, power-law usable demands, and a conjectured limsup/liminf classification. Meyerovitch's entropy-dimension classification is the exact precedent in form.

## Files

| Path | Contents |
|---|---|
| `paper/main.pdf` | Built manuscript |
| `paper/main.tex`, `paper/sections/`, `paper/refs.bib` | LaTeX source and bibliography, with `plainurl` |
| `paper/abstract-arxiv.txt` | Submission abstract, at most 1920 characters |
| `anc/` | All v1 checks plus finite reader, discrepancy, compression, Jensen, extraction, complementary-gate and stop-or-continue checks |
| `verify/` | Preserved independent v1 finite-model engine and recorded output |

## Build

From `paper/`, run `latexmk -pdf main`, or `pdflatex -interaction=nonstopmode -halt-on-error main`, `bibtex main`, then repeat pdflatex until references settle. The final log must have no LaTeX warnings or overfull/underfull boxes. `paper/prepare_assets.py` regenerates the abstract, citation metadata and SHA-256 manifests with LF endings. With `--bib PATH` it also regenerates the curated bibliography, keeping `refs-extra.bib`. It runs no Git command and publishes nothing.

`paper/check_artifacts.py` checks the PDF, rendered pages, metadata and manifests. Render the pages first, for example `pdftoppm -r 60 -png main.pdf build/render/page` from `paper/` (Pillow, pypdf, pdfplumber, PyYAML and Poppler's `pdftoppm` are required). It writes contact sheets and `artifact-checks.json` under `paper/build/`.

The manuscript cites [The price of precision](https://doi.org/10.5281/zenodo.23697346), [its game companion](https://doi.org/10.5281/zenodo.23697255), and [The heat price of precision](https://doi.org/10.5281/zenodo.23701732).

## Checks and status

The lower bounds rest on written proofs. Independent audits and finite computations are described in the paper and `anc/README.md`. A Lean formalization of the version 1.0.0 core is **in progress and not complete**. The newer sections are not yet formalized. No completed Lean verification is claimed. This preprint has not been peer reviewed.

## License

Text, LaTeX and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0, at the user's option. See RIGHTS.md, NOTICE and the license files.
