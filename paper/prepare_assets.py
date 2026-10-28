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
ABSTRACT = "Which numbers can be the entanglement price of perfection for one fixed finite game? The positive dimension exponents of finite rational Boolean constraint-system games of quantum value one are exactly the positive $\\Delta^0_2$ reals. For every such $\\alpha$ we construct one game, with no finite-dimensional perfect strategy, whose least local dimension satisfies $\\log_2D_G(\\varepsilon)=\\alpha\\log_2(1/\\varepsilon)+o(\\log(1/\\varepsilon))$. The infimum one-way distillable entanglement of the original mixed strategy state has the same coefficient. This is a realization theorem for usable entanglement; its full spectrum remains open. A finite stop-or-continue program combines finite perfect witnesses from MIP*=RE with a scalar tail verifier for an arbitrary computable convergent rational sequence. Per-gate data are loaded once and held fixed while checked. Matrix-approximable traces give the lower bound; finite threshold histories with sublinear logarithmic witness overhead give matching models. The left-c.e. construction, exact-trace obstruction and non-left-c.e. example of version 2.0.0 become steps toward the classification. In the reset model of the companion heat paper, local-reset heat has coefficient $2\\alpha$, while joint-reset heat stays bounded: the order of communication and reset changes the asymptotic cost of one device. With recovery before reset, the critical quantum return rate is $\\alpha$ in the companion block model. Every positive $\\Delta^0_2$ local-heat coefficient is thus realized; the full heat spectrum and the computability of the finite-precision heat function remain open. The version-1.0.0 halting-degree game and its proofs are retained. Meyerovitch's classification of entropy dimensions is the precedent in form; here the classified exponent is a nonlocal-game dimension cost."
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
    'type: software', 'title: '+json.dumps(TITLE), 'version: 3.0.0', 'doi: 10.5281/zenodo.23701733',
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
    '  year: 2026', '  version: 3.0.0',
    '  doi: 10.5281/zenodo.23701733',
    '  notes: "Preprint. Lean formalization of the version 1.0.0 core is in progress and not complete; the newer sections are not yet formalized. Concept DOI (latest version): 10.5281/zenodo.23701733. Version 1.0.0 DOI: 10.5281/zenodo.23701734. Version 2.0.0 DOI: 10.5281/zenodo.23717986. Text CC BY 4.0; scripts MIT or Apache 2.0; see RIGHTS.md."', ''
])
(ROOT / 'CITATION.cff').write_text(cff, encoding='utf-8', newline='\n')
zenodo = {
    'title':TITLE, 'upload_type':'publication', 'publication_type':'preprint',
    'version':'3.0.0',
    'creators':[{'name':'Douglas, Seth'},{'name':'Mghirbi, Nidhal'}],
    'description':'<p>'+ABSTRACT+'</p>',
    'keywords':['nonlocal games','dimension exponent','Boolean constraint systems','computability'],
    'access_right':'open','license':'cc-by-4.0','language':'eng',
    'notes':'Preprint. It has not been peer reviewed. Text and documentation: CC BY 4.0. Scripts: MIT or Apache 2.0. A Lean formalization of the version 1.0.0 core is in progress and not complete; the newer sections are not yet formalized. Version 2.0.0 DOI: 10.5281/zenodo.23717986. Version 1.0.0 DOI: 10.5281/zenodo.23701734; concept DOI (latest version): 10.5281/zenodo.23701733.'
}
zenodo['related_identifiers'] = [
    {'identifier':'10.5281/zenodo.23717986','scheme':'doi','relation':'isNewVersionOf'},
    {'identifier':'10.5281/zenodo.23701734','scheme':'doi','relation':'isNewVersionOf'},
    {'identifier':'10.5281/zenodo.23701733','scheme':'doi','relation':'isVersionOf'}]
(ROOT / '.zenodo.json').write_text(json.dumps(zenodo, indent=2)+'\n', encoding='utf-8', newline='\n')

lines = []
for path in sorted(ANC.rglob('*')):
    if path.is_file() and path.name != 'SHA256SUMS' and path.relative_to(ANC).as_posix() not in ('gate/toy-results.json', 'spectrum/numerical_results.json', 'classification/toy-results.json', 'classification/matrix-interface-results.json', 'classification/upper-checkpoint.json', 'classification/toy_results.json', 'classification/operator_level_results.json'):
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
