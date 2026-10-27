# A nonlocal game whose dimension exponent is uncomputable

Seth Douglas and Nidhal Mghirbi. Version 1.0.0, October 2026.

## Abstract

Can uncomputability occur in the resource law of one fixed finite nonlocal game, rather than in a problem whose input is a game? We construct a finite two-player Boolean constraint-system game with rational question probabilities, quantum value one, and no finite-dimensional perfect strategy. If $D(\varepsilon)$ is the least local dimension needed to win with probability at least $1-\varepsilon$, then $\lim_{n\to\infty}\log_2 D(2^{-n})/n=(3+\theta_K)/4$, where $\theta_K=\sum_{e\in K}4^{-(e+1)}$ and $K$ is the halting set. This exponent has the Turing degree of $K$. The construction combines finite operator relations for three Cantor clocks, a counter program with forced initialization, and a conditional clock that charges dimension for halting inputs. A Boolean compiler preserves weighted precision linearly and converts flat models to strategies with quadratic loss. The lower bound holds in every density matrix. Explicit finite models attain the same rate. The flag-density lower bound uses compactness without an effective modulus; convergence to the dimension exponent has no computable certified rate.

The stated result concerns local dimension. An independent proof check and an independent finite-model engine are described in the methods section of the paper and in `anc/README.md`.

## Files

| Path | Contents |
|---|---|
| `paper/main.pdf` | Built manuscript |
| `paper/main.tex`, `paper/sections/`, `paper/refs.bib` | LaTeX source and bibliography, using `plainurl` |
| `paper/abstract-arxiv.txt` | Submission abstract, at most 1920 characters |
| `anc/` | Finite-model audit script, gadget checks, proof-check scripts, recorded outputs and hashes |
| `verify/` | Independent finite-model engine, with its recorded output |

## Build

From `paper/`, run `latexmk -pdf main`. Equivalently, run `pdflatex -interaction=nonstopmode -halt-on-error main`, then `bibtex main`, then repeat the pdflatex command until references settle. The final log must have no LaTeX warnings or overfull/underfull boxes. `paper/prepare_assets.py` regenerates the arXiv abstract, root citation metadata and ancillary hashes; with `--bib PATH` it also regenerates the curated bibliography from the source bibliography at `PATH`. It does not use git.

Optional editorial QA is provided by `paper/check_artifacts.py`; it reads rendered pages and metadata and requires Pillow, pypdf, pdfplumber and PyYAML. Poppler's `pdftoppm` produces the rendered pages. These tools are not required to compile the LaTeX source.

The manuscript cites *The price of precision* ([DOI](https://doi.org/10.5281/zenodo.23697346)) and its companion, *An explicit nonlocal game of quantum value one that needs exponential entanglement* ([DOI](https://doi.org/10.5281/zenodo.23697255)).

## Checks and status

See `anc/README.md` for exact scope and commands. Finite computations support the proofs; the arbitrary-state lower bound rests on the written argument. No Lean formalization exists yet. One is planned. This draft has not been peer reviewed.

## License

Text, LaTeX and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0, at the user's option. See RIGHTS.md, NOTICE, and the three license files. CITATION.cff and .zenodo.json are local metadata, not evidence of release or upload.
