"""Prepare requested local metadata and bibliography; does not use git or publish.
All writes are restricted to the explicitly requested paper/anc files and root
metadata. The curated bibliography is regenerated only when the source
bibliography input defaults to refs-base.bib; --bib PATH overrides it read-only.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

PAPER = Path(__file__).resolve().parent
ROOT = PAPER.parent
ANC = ROOT / 'anc'
TITLE = 'The uncomputable price of precision'
ABSTRACT = "Which pairs can be the lower and upper entanglement price of perfection for one fixed game? For finite rational Boolean constraint-system games of quantum value one, the positive finite logarithmic dimension-exponent pairs are exactly $0<L\\le U$ with $L\\in\\Sigma^0_2$ and $U\\in\\Pi^0_2$. Every pair has a matched one-way distillable-entanglement realization on the original mixed strategy state. The diagonal recovers exactly the positive $\\Delta^0_2$ coefficients and gives a proof using no $\\mathrm{MIP}^*=\\mathrm{RE}$ witness. For a counter program with polynomial pulse delay, positive lower one-density and one-count $k$, a carry-checker construction gives $\\log_2D_G(2^{-n})=\\Lambda+(m/2)k(\\Lambda)+O(\\log n)$, with the same usable profile, where $m,q\\ge1$ are fixed integers and $\\Lambda=\\lfloor n/(2q)\\rfloor$. At the power scale, every admissible endpoint pair in $(0,1]$ has matched log-dimension, usable, pure-entropy and formation realizations; the dimension endpoint conditions are also necessary. The full usable endpoint ceilings remain open. With linear slope bounds, target profiles computable in logarithmic space are realized to $O(\\log n)$, and sublinear-space targets modulo $o(n)$. Every dimension profile with finite upper exponent is computable within doubly exponential time; some computable bounded-increment profiles with any admissible distinct endpoints are not realized by any game even modulo $o(n)$. This separates endpoint classification from whole-profile realization. The witness-based proof also yields the exact-trace barrier and the projection-minimum classification. In the companion reset model, local-heat endpoint pairs double while joint-reset heat stays bounded. Meyerovitch's entropy dimensions, Hochman-Meyerovitch's local-rule spectra and Sapir-Birget-Rips's time conditions are precedents in form; the invariants here are fixed-game precision costs."
assert len(ABSTRACT) <= 1920

# Keep every submission surface literal and preserve the page-one notice wording.
abstract_path=PAPER/'sections/abstract.tex'
previous=abstract_path.read_text(encoding='utf-8')
notice=previous[previous.index(r'\noindent\emph{'):].split(r'\medskip')[0].strip()
abstract_path.write_text('\\begin{abstract}\n'+ABSTRACT+'\n\\end{abstract}\n'+notice+'\n\n\\medskip\n\\noindent{\\small Concept DOI: \\href{https://doi.org/10.5281/zenodo.23701733}{10.5281/zenodo.23701733}.}\n',encoding='utf-8',newline='\n')
readme=ROOT/'README.md';text=readme.read_text(encoding='utf-8');start=text.index('## Abstract');end=text.index('\n## ',start+1)
readme.write_text(text[:start]+'## Abstract\n\n'+ABSTRACT+'\n'+text[end:],encoding='utf-8',newline='\n')

(PAPER / 'abstract-arxiv.txt').write_text(ABSTRACT+'\n', encoding='utf-8', newline='\n')

parser = argparse.ArgumentParser()
parser.add_argument('--bib', type=Path, default=PAPER/'refs-base.bib', help='read-only base bibliography (default: refs-base.bib)')
args = parser.parse_args()
keys = ['CM14', 'CLS17', 'Slo20', 'Slo19', 'SV18', 'Slo18', 'MSZ23',
        'FKMPRSZ25', 'HM10', 'Hol73', 'MNY22', 'DM-game']
if args.bib:
    source = args.bib.read_text(encoding='utf-8')
    entries = {}
    for block in re.split(r'(?m)(?=^@)', source):
        match = re.match(r'@\w+\{([^,]+),', block)
        if match:
            entries[match.group(1)] = block.strip()
    selected = '\n\n'.join(entries[k] for k in keys)
    selected = selected.replace(r'\companionref', 'Version 1.0.0, Zenodo. Unrefereed preprint')
    selected = selected.replace('Published online. Lemma~3.9 has the same number and statement in arXiv versions~1 and~2',
                                'Published online. Result numbers refer to arXiv version~2')
    (PAPER / 'refs.bib').write_text(selected+'\n\n'+(PAPER / 'refs-extra.bib').read_text(encoding='utf-8'), encoding='utf-8', newline='\n')

authors = [{'family-names':'Douglas','given-names':'Seth'},
           {'family-names':'Mghirbi','given-names':'Nidhal'}]
cff = '\n'.join([
    'cff-version: 1.2.0',
    'message: "Please cite the paper; this repository supplies its source and ancillary checks."',
    'type: software', 'title: '+json.dumps(TITLE), 'version: 4.0.0', 'doi: 10.5281/zenodo.23701733',
    'repository-code: "https://github.com/Apsiape/uncomputable-dimension-exponent"',
    'abstract: '+json.dumps(ABSTRACT),
    'license:', '  - CC-BY-4.0', '  - MIT', '  - Apache-2.0',
    'authors:',
    '  - family-names: Douglas', '    given-names: Seth',
    '  - family-names: Mghirbi', '    given-names: Nidhal',
    'keywords:', '  - nonlocal games', '  - dimension exponent',
    '  - Boolean constraint systems', '  - computability',
    'preferred-citation:', '  type: generic', '  title: '+json.dumps(TITLE),
    '  authors:', '    - family-names: Douglas', '      given-names: Seth',
    '    - family-names: Mghirbi', '      given-names: Nidhal',
    '  year: 2026', '  version: 4.0.0',
    '  doi: 10.5281/zenodo.23701733',
    '  notes: "Preprint. Lean formalization of Sections 2--10 is in progress and not complete; the remaining sections, power-scale part and profile part are not yet formalized. Concept DOI: 10.5281/zenodo.23701733. Text CC BY 4.0; scripts MIT or Apache 2.0; see RIGHTS.md."', ''
])
(ROOT / 'CITATION.cff').write_text(cff, encoding='utf-8', newline='\n')
zenodo = {
    'title':TITLE, 'upload_type':'publication', 'publication_type':'preprint',
    'version':'4.0.0',
    'creators':[{'name':'Douglas, Seth'},{'name':'Mghirbi, Nidhal'}],
    'description':'<p>'+ABSTRACT+'</p>',
    'keywords':['nonlocal games','dimension exponent','Boolean constraint systems','computability'],
    'access_right':'open','license':'cc-by-4.0','language':'eng',
    'notes':'Preprint. It has not been peer reviewed. Text and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0. A Lean formalization of Sections 2--10 is in progress and not complete; the remaining sections, power-scale part and profile part are not yet formalized. Concept DOI: 10.5281/zenodo.23701733.'
}
zenodo['related_identifiers'] = [{'identifier':'10.5281/zenodo.23701733','scheme':'doi','relation':'isVersionOf'}]
(ROOT / '.zenodo.json').write_text(json.dumps(zenodo, indent=2)+'\n', encoding='utf-8', newline='\n')

lines = []
for path in sorted(ANC.rglob('*')):
    if path.is_file() and path.name != 'SHA256SUMS' and not (path.relative_to(ANC).parts[0] in ('power','profiles','frontiers') and path.suffix in ('.json','.log') and 'recorded' not in path.relative_to(ANC).parts) and path.relative_to(ANC).as_posix() not in ('audit/model_results.json', 'audit/defects_N4.csv', 'audit/defects_N6.csv', 'audit/defects_N8.csv', 'gate/toy-results.json', 'spectrum/numerical_results.json', 'classification/toy-results.json', 'classification/matrix-interface-results.json', 'classification/upper-checkpoint.json', 'classification/toy_results.json', 'classification/operator_level_results.json'):
        lines.append(hashlib.sha256(path.read_bytes()).hexdigest()+'  '+path.relative_to(ANC).as_posix())
(ANC / 'SHA256SUMS').write_text('\n'.join(lines)+'\n', encoding='ascii', newline='\n')
print('arXiv abstract characters:',len(ABSTRACT))
print('Bibliography entries:',len(keys)+len(re.findall(r'(?m)^@', (PAPER / 'refs-extra.bib').read_text())))
print('Ancillary files hashed:',len(lines))

VERIFY = ROOT / 'verify'
for manifest in VERIFY.rglob('SHA256SUMS'):
    entries = []
    for path in sorted(manifest.parent.rglob('*')):
        if path.is_file() and path != manifest and '__pycache__' not in path.parts:
            entries.append(hashlib.sha256(path.read_bytes()).hexdigest()+'  '+path.relative_to(manifest.parent).as_posix())
    manifest.write_text('\n'.join(entries)+'\n', encoding='ascii', newline='\n')
