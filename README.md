# The uncomputable price of precision

Seth Douglas and Nidhal Mghirbi. Version 4.0.0, October 2026. Concept DOI: [10.5281/zenodo.23701733](https://doi.org/10.5281/zenodo.23701733).

## Abstract

Which pairs can be the lower and upper entanglement price of perfection for one fixed game? For finite rational Boolean constraint-system games of quantum value one, the positive finite logarithmic dimension-exponent pairs are exactly $0<L\le U$ with $L\in\Sigma^0_2$ and $U\in\Pi^0_2$. Every pair has a matched one-way distillable-entanglement realization on the original mixed strategy state. The diagonal recovers exactly the positive $\Delta^0_2$ coefficients and gives a proof using no $\mathrm{MIP}^*=\mathrm{RE}$ witness. For a counter program with polynomial pulse delay, positive lower one-density and one-count $k$, a carry-checker construction gives $\log_2D_G(2^{-n})=\Lambda+(m/2)k(\Lambda)+O(\log n)$, with the same usable profile, where $m,q\ge1$ are fixed integers and $\Lambda=\lfloor n/(2q)\rfloor$. At the power scale, every admissible endpoint pair in $(0,1]$ has matched log-dimension, usable, pure-entropy and formation realizations; the dimension endpoint conditions are also necessary. The full usable endpoint ceilings remain open. With linear slope bounds, target profiles computable in logarithmic space are realized to $O(\log n)$, and sublinear-space targets modulo $o(n)$. Every dimension profile with finite upper exponent is computable within doubly exponential time; some computable bounded-increment profiles with any admissible distinct endpoints are not realized by any game even modulo $o(n)$. This separates endpoint classification from whole-profile realization. The witness-based proof also yields the exact-trace barrier and the projection-minimum classification. In the companion reset model, local-heat endpoint pairs double while joint-reset heat stays bounded. Meyerovitch's entropy dimensions, Hochman-Meyerovitch's local-rule spectra and Sapir-Birget-Rips's time conditions are precedents in form; the invariants here are fixed-game precision costs.

## Results

- The positive dimension exponents of finite rational BCS games of quantum value one are exactly the positive Delta^0_2 reals.
- Every positive Delta^0_2 real also occurs as the logarithmic one-way distillable-entanglement coefficient of the **original mixed state**. The full usable spectrum remains open.
- A stop-or-continue program with per-gate loaded data gives a matrix-approximable flag minimum of `1-theta` for every computable convergent rational approximation to theta, with matched finite models.
- Local-reset heat has twice the matched coefficient; joint-reset heat of the same device stays bounded. The claim concerns limiting coefficients, not computability of a finite-precision heat function.

The approximable projection minima are classified separately as the reals in [0,1] left-c.e. relative to the halting problem, with an explicit obstruction to a matched witness budget. In the companion block model, the critical quantum-recovery rate equals the dimension coefficient; it is undecidable uniformly even under a two-rational promise. The full local-heat spectrum has an arithmetic upper bound and remains open. Real and complex dimension exponents agree, and positive reweighting preserves the exponents.

The power-scale part proves matching log-dimension and original-state usable exponents for every Delta^0_2 beta in (0,1]. The existing exponents of log dimension, pure entropy and formation in that interval are exactly that class. Its finite program, clock localization, moment models and full proofs are included. The full usable ceiling and exponents above one remain open. The profile part classifies logarithmic dimension endpoint pairs, proves a second witness-free realization, realizes space-bounded target profiles and gives a doubly exponential time restriction with computable non-realizable examples. The halting construction, reader, extraction, exact-trace barrier, complementary gate and stop-or-continue results form the logarithmic-scale development. Meyerovitch's entropy dimensions and programmed Dehn spectra receive explicit credit.

## Files

| Path | Contents |
|---|---|
| `paper/main.pdf` | Built manuscript |
| `paper/main.tex`, `paper/sections/`, `paper/refs.bib` | LaTeX source and bibliography, with `plainurl` |
| `paper/abstract-arxiv.txt` | Submission abstract, at most 1920 characters |
| `anc/` | Finite-model checks plus finite reader, discrepancy, compression, Jensen, extraction, complementary-gate and stop-or-continue checks |
| `verify/` | Independent finite-model engine and recorded output |

## Build

Run `python paper/build.py` for four plain pdflatex passes and BibTeX, with shell escape disabled. Intermediate files go to a fresh temporary directory outside the source tree, printed on completion. Use `--build-dir BUILD_DIR` to choose an outside-tree directory. The final PDF and bibliography are copied to `paper/`. The final log must have no warnings or overfull/underfull boxes.

`paper/prepare_assets.py` regenerates the abstract, citation metadata and SHA-256 manifests with LF endings. It regenerates `refs.bib` from the maintained `refs-base.bib` and `refs-extra.bib` inputs; `--bib PATH` overrides the base input read-only. It runs no Git command and publishes nothing.

For artifact checks, create an outside-tree render directory and run `pdftoppm -r 60 -png paper/main.pdf RENDER_DIR/page`. Then run `python paper/check_artifacts.py --render-dir RENDER_DIR --log-dir BUILD_DIR`; `--output-dir CHECK_DIR` selects an outside-tree directory for contact sheets and the check report, otherwise a fresh temporary directory is used. Pillow, pypdf, pdfplumber and PyYAML are required. Build and rendering directories are not distributed.

The manuscript cites [The price of precision](https://doi.org/10.5281/zenodo.23697346), [its game companion](https://doi.org/10.5281/zenodo.23697255), and [The heat price of precision](https://doi.org/10.5281/zenodo.23701732).

The exact standalone upload sources are in `paper/arxiv/`; with no `refs.bib` present they build using the supplied `main.bbl`, which is input directly. Run plain `pdflatex main.tex` repeatedly until references settle; BibTeX is not run in this folder (there is no bibliography-style directive for it).

## Checks and status

The lower bounds rest on written proofs. Finite computations and their limits are described in the paper and `anc/README.md`. A Lean formalization of Sections 2--10 is **in progress and not complete**. Sections 11--17, the power-scale part and the profile part are not yet formalized. No completed Lean verification is claimed. This preprint has not been peer reviewed.

## License

Text, LaTeX and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0, at the user's option. See RIGHTS.md, NOTICE and the license files.
