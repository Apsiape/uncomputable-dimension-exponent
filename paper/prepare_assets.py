"""Prepare requested local metadata and bibliography; does not use git or publish.
All writes are restricted to the explicitly requested paper/anc files and root
metadata. The curated bibliography is regenerated only when the source
bibliography is given as `--bib PATH`; that file is read only.
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
ABSTRACT = 'Which numbers can be the entanglement price of perfection for one fixed finite game? Every positive left-computably-enumerable real occurs, and the exponents go strictly beyond this class. For each such $\\alpha$ we construct a finite Boolean constraint-system game of quantum value one, with no finite-dimensional perfect strategy, whose least local dimension obeys $\\log_2D_G(\\varepsilon)=\\alpha\\log_2(1/\\varepsilon)+o(\\log(1/\\varepsilon))$. The infimum one-way distillable entanglement of the original mixed strategy state has the same coefficient. A second construction realizes $\\alpha=(4-\\theta_K)/4$, a noncomputable right-c.e. real that is not left-c.e., where $\\theta_K=\\sum_{e\\in K}4^{-(e+1)}$ and $K$ is the halting set. As in our earlier work, every dimension exponent is $\\Delta^0_2$ whenever its limit exists. In the reset model of our companion paper on the heat price of precision, local-reset heat has coefficient $2\\alpha$, while joint-reset heat stays bounded. The halting-degree game of version 1.0.0 and its proofs are retained. A finite address reader, extra clocks and polynomial residual powers give the left-c.e. realization; triangular extraction gives the mixed-state bound. To escape the exact-trace barrier, a fixed polynomial-testing program uses finite perfect witnesses from MIP*=RE, admitted with sublinear logarithmic dimension overhead. Exact and matrix-approximable trace minima then differ. Both left-c.e. and non-left-c.e. uncomputable examples accumulate at zero. The full spectra remain open.'
assert len(ABSTRACT) <= 1920
(PAPER / 'abstract-arxiv.txt').write_text(ABSTRACT+'\n', encoding='utf-8', newline='\n')

parser = argparse.ArgumentParser()
parser.add_argument('--bib', type=Path, help='source bibliography from which refs.bib is curated')
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
    'type: software', 'title: '+json.dumps(TITLE), 'version: 2.0.0', 'doi: 10.5281/zenodo.23701733',
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
    '  year: 2026', '  version: 2.0.0',
    '  doi: 10.5281/zenodo.23701733',
    '  notes: "Preprint. Lean formalization of the version 1.0.0 core is in progress and not complete. Concept DOI (latest version): 10.5281/zenodo.23701733. Version 1.0.0 DOI: 10.5281/zenodo.23701734. Text CC BY 4.0; scripts MIT or Apache 2.0; see RIGHTS.md."', ''
])
(ROOT / 'CITATION.cff').write_text(cff, encoding='utf-8', newline='\n')
zenodo = {
    'title':TITLE, 'upload_type':'publication', 'publication_type':'preprint',
    'version':'2.0.0',
    'creators':[{'name':'Douglas, Seth'},{'name':'Mghirbi, Nidhal'}],
    'description':'<p>'+ABSTRACT+'</p>',
    'keywords':['nonlocal games','dimension exponent','Boolean constraint systems','computability'],
    'access_right':'open','license':'cc-by-4.0','language':'eng',
    'notes':'Preprint. It has not been peer reviewed. Text and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0. A Lean formalization of the version 1.0.0 core is in progress and not complete. Version 1.0.0 DOI: 10.5281/zenodo.23701734; concept DOI (latest version): 10.5281/zenodo.23701733.'
}
zenodo['related_identifiers'] = [
    {'identifier':'10.5281/zenodo.23701734','scheme':'doi','relation':'isNewVersionOf'},
    {'identifier':'10.5281/zenodo.23701733','scheme':'doi','relation':'isVersionOf'}]
(ROOT / '.zenodo.json').write_text(json.dumps(zenodo, indent=2)+'\n', encoding='utf-8', newline='\n')

lines = []
for path in sorted(ANC.rglob('*')):
    if path.is_file() and path.name != 'SHA256SUMS' and path.relative_to(ANC).as_posix() not in ('gate/toy-results.json', 'spectrum/numerical_results.json'):
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
