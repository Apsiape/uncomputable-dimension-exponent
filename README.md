# The uncomputable price of precision

Seth Douglas and Nidhal Mghirbi. Version 2.0.0, October 2026.

**Concept DOI (latest version): [10.5281/zenodo.23701733](https://doi.org/10.5281/zenodo.23701733).** The released v1.0.0 is [A nonlocal game whose dimension exponent is uncomputable](https://doi.org/10.5281/zenodo.23701734).

## Abstract

Which numbers can be the entanglement price of perfection for one fixed finite game? Every positive left-computably-enumerable real occurs, and the exponents go strictly beyond this class. For each such $\alpha$ we construct a finite Boolean constraint-system game of quantum value one, with no finite-dimensional perfect strategy, whose least local dimension obeys $\log_2D_G(\varepsilon)=\alpha\log_2(1/\varepsilon)+o(\log(1/\varepsilon))$. The infimum one-way distillable entanglement of the original mixed strategy state has the same coefficient. A second construction realizes $\alpha=(4-\theta_K)/4$, a noncomputable right-c.e. real that is not left-c.e., where $\theta_K=\sum_{e\in K}4^{-(e+1)}$ and $K$ is the halting set. As in our earlier work, every dimension exponent is $\Delta^0_2$ whenever its limit exists. In the reset model of our companion paper on the heat price of precision, local-reset heat has coefficient $2\alpha$, while joint-reset heat stays bounded. The halting-degree game of version 1.0.0 and its proofs are retained. A finite address reader, extra clocks and polynomial residual powers give the left-c.e. realization; triangular extraction gives the mixed-state bound. To escape the exact-trace barrier, a fixed polynomial-testing program uses finite perfect witnesses from MIP*=RE, admitted with sublinear logarithmic dimension overhead. Exact and matrix-approximable trace minima then differ. Both left-c.e. and non-left-c.e. uncomputable examples accumulate at zero. The full spectra remain open.

## What version 2 adds

- Every positive left-c.e. real is realized by a fixed finite BCS game as both a dimension exponent and a logarithmic usable-entanglement coefficient.
- The complementary game realizes $(4-\theta_K)/4$, which is right-c.e. and not left-c.e.; the positive BCS dimension spectrum strictly contains the positive left-c.e. reals and lies in $\Delta^0_2$.
- Triangular extraction with an inactive outcome applies to the **original mixed state**, with an explicit Alice-to-Bob protocol and hashing.
- Local-reset heat has twice that coefficient; joint-reset heat of the same game stays bounded. The order of reset and quantum reunion matters.

The v1 halting-degree game, results, proofs and checks are retained. The positive-computable-real inclusion conjectured in the discussion of Problem 18.3(i) of *The price of precision* is proved and strengthened. The full coefficient sets and the zero-coefficient question remain open.

## Files

| Path | Contents |
|---|---|
| `paper/main.pdf` | Built manuscript |
| `paper/main.tex`, `paper/sections/`, `paper/refs.bib` | LaTeX source and bibliography, with `plainurl` |
| `paper/abstract-arxiv.txt` | Submission abstract, at most 1920 characters |
| `anc/` | All v1 checks plus finite reader, discrepancy, compression, Jensen, extraction and complementary-gate checks |
| `verify/` | Preserved independent v1 finite-model engine and recorded output |

## Build

From `paper/`, run `latexmk -pdf main`, or `pdflatex -interaction=nonstopmode -halt-on-error main`, `bibtex main`, then repeat pdflatex until references settle. The final log must have no LaTeX warnings or overfull/underfull boxes. `paper/prepare_assets.py` regenerates the abstract, citation metadata and SHA-256 manifests with LF endings. With `--bib PATH` it also regenerates the curated bibliography, keeping `refs-extra.bib`. It runs no Git command and publishes nothing.

`paper/check_artifacts.py` checks the PDF, rendered pages, metadata and manifests (Pillow, pypdf, pdfplumber, PyYAML and Poppler's `pdftoppm` are required).

The manuscript cites [The price of precision](https://doi.org/10.5281/zenodo.23697346), [its game companion](https://doi.org/10.5281/zenodo.23697255), and [The heat price of precision](https://doi.org/10.5281/zenodo.23701732).

## Checks and status

The lower bounds rest on written proofs. Independent audits and finite computations are described in the paper and `anc/README.md`. A Lean formalization of the version 1.0.0 core is **in progress and not complete**. No completed Lean verification is claimed. This preprint has not been peer reviewed.

## License

Text, LaTeX and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0, at the user's option. See RIGHTS.md, NOTICE and the license files.
