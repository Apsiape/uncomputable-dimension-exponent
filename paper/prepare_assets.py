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
TITLE = 'A nonlocal game whose dimension exponent is uncomputable'
ABSTRACT = r'''Can uncomputability occur in the resource law of one fixed finite nonlocal game, rather than in a problem whose input is a game? We construct a finite two-player Boolean constraint-system game with rational question probabilities, quantum value one, and no finite-dimensional perfect strategy. If $D(\varepsilon)$ is the least local dimension needed to win with probability at least $1-\varepsilon$, then $\lim_{n\to\infty}\log_2 D(2^{-n})/n=(3+\theta_K)/4$, where $\theta_K=\sum_{e\in K}4^{-(e+1)}$ and $K$ is the halting set. This exponent has the Turing degree of $K$. The construction combines finite operator relations for three Cantor clocks, a counter program with forced initialization, and a conditional clock that charges dimension for halting inputs. A Boolean compiler preserves weighted precision linearly and converts flat models to strategies with quadratic loss. The lower bound holds in every density matrix. Explicit finite models attain the same rate. The flag-density lower bound uses compactness without an effective modulus; convergence to the dimension exponent has no computable certified rate.'''
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
    'type: software', 'title: '+json.dumps(TITLE), 'version: 1.0.0',
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
    '  year: 2026', '  version: 1.0.0',
    '  notes: "Preprint. Text CC BY 4.0; scripts MIT or Apache 2.0; see RIGHTS.md."', ''
])
(ROOT / 'CITATION.cff').write_text(cff, encoding='utf-8', newline='\n')
zenodo = {
    'title':TITLE, 'upload_type':'publication', 'publication_type':'preprint',
    'version':'1.0.0',
    'creators':[{'name':'Douglas, Seth'},{'name':'Mghirbi, Nidhal'}],
    'description':'<p>'+ABSTRACT+'</p>',
    'keywords':['nonlocal games','dimension exponent','Boolean constraint systems','computability'],
    'access_right':'open','license':'cc-by-4.0','language':'eng',
    'notes':'Preprint. It has not been peer reviewed. Text and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0. No Lean formalization yet; one is planned.'
}
(ROOT / '.zenodo.json').write_text(json.dumps(zenodo, indent=2)+'\n', encoding='utf-8', newline='\n')

lines = []
for path in sorted(ANC.rglob('*')):
    if path.is_file() and path.name != 'SHA256SUMS':
        lines.append(hashlib.sha256(path.read_bytes()).hexdigest()+'  '+path.relative_to(ANC).as_posix())
(ANC / 'SHA256SUMS').write_text('\n'.join(lines)+'\n', encoding='ascii', newline='\n')
print('arXiv abstract characters:',len(ABSTRACT))
print('Bibliography entries:',len(keys)+len(re.findall(r'(?m)^@', (PAPER / 'refs-extra.bib').read_text())))
print('Ancillary files hashed:',len(lines))
