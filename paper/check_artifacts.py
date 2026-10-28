"""Check the built PDF, metadata, archived hashes and protected version-1 files."""
import os
os.environ['OMP_NUM_THREADS']='1'
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
from PIL import Image, ImageDraw
from pypdf import PdfReader
import pdfplumber
import yaml

P=Path(__file__).resolve().parent
R=P.parent
B=P/'build'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--render-dir',type=Path,default=B/'render')
parser.add_argument('--log-dir',type=Path,default=B/'compile')
parser.add_argument('--pdf',type=Path,default=P/'main.pdf')
args=parser.parse_args()
B.mkdir(exist_ok=True)
pages=sorted(args.render_dir.glob('page-*.png'))
reader=PdfReader(args.pdf)
assert pages and len(pages)==len(reader.pages)
for start in range(0,len(pages),12):
    sheet=Image.new('RGB',(1050,2080),'white')
    draw=ImageDraw.Draw(sheet)
    for index,path in enumerate(pages[start:start+12]):
        with Image.open(path) as source:
            picture=source.convert('RGB')
        picture.thumbnail((330,478))
        x,y=(index%3)*350+10,(index//3)*520+24
        sheet.paste(picture,(x,y))
        draw.text((x,y-19),'Page '+str(start+index+1),fill='black')
    sheet.save(B/f'contact-{start//12+1}.png')
text='\n'.join(page.extract_text() or '' for page in reader.pages)
assert '??' not in text
abstract=(P/'abstract-arxiv.txt').read_text(encoding='utf-8').strip()
assert len(abstract)<=1920
assert abstract in (P/'sections/abstract.tex').read_text(encoding='utf-8')
assert abstract in (R/'README.md').read_text(encoding='utf-8')
cff=yaml.safe_load((R/'CITATION.cff').read_text(encoding='utf-8'))
zen=json.loads((R/'.zenodo.json').read_text(encoding='utf-8'))
asset_tree=ast.parse((P/'prepare_assets.py').read_text(encoding='utf-8'))
asset_abstract=next(ast.literal_eval(n.value) for n in asset_tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='ABSTRACT' for t in n.targets))
assert asset_abstract==abstract
assert cff['abstract']==abstract
assert zen['description']=='<p>'+abstract+'</p>'
assert cff['doi']==cff['preferred-citation']['doi']=='10.5281/zenodo.23701733'
assert 'doi' not in zen
assert cff['title']==zen['title']=='The uncomputable price of precision'
assert cff['version']==cff['preferred-citation']['version']==zen['version']=='3.0.0'
assert [a['family-names'] for a in cff['authors']]==['Douglas','Mghirbi']
assert [a['name'] for a in zen['creators']]==['Douglas, Seth','Mghirbi, Nidhal']
assert 'in progress and not complete' in zen['notes']
assert all((R/name).is_file() for name in ('NOTICE','RIGHTS.md','LICENSE-CC-BY-4.0.txt','LICENSE-MIT.txt','LICENSE-APACHE-2.0.txt'))
log=(args.log_dir/'main.log').read_text(errors='replace')
warnings=re.findall(r'(?m)^(?:LaTeX Warning|Package .* Warning|Overfull|Underfull).*$',log)
assert not warnings,warnings
assert not re.search(r'(?i)warning--|error message',(args.log_dir/'main.blg').read_text())
manifest=R/'anc/SHA256SUMS'
assert b'\r' not in manifest.read_bytes()
archived=[]
for line in manifest.read_text().splitlines():
    digest,rel=line.split('  ',1)
    assert hashlib.sha256((R/'anc'/rel).read_bytes()).hexdigest()==digest,rel
    archived.append(rel)
assert 'gate/toy-results.json' not in archived
assert 'spectrum/numerical_results.json' not in archived
for manifest in (R/'verify').rglob('SHA256SUMS'):
    assert b'\r' not in manifest.read_bytes()
    for line in manifest.read_text().splitlines():
        digest,rel=line.split('  ',1)
        assert hashlib.sha256((manifest.parent/rel).read_bytes()).hexdigest()==digest,rel
baseline=json.loads((P/'preservation-baseline.json').read_text(encoding='utf-8'))
for entry in baseline['proof_files']+baseline['check_files']:
    assert hashlib.sha256((R/entry['path']).read_bytes()).hexdigest()==entry['sha256'],entry['path']
extents=[]
with pdfplumber.open(args.pdf) as pdf:
    for number,page in enumerate(pdf.pages,1):
        chars=[c for c in page.chars if c.get('text','').strip()]
        assert all(-.1<=c['x0'] and c['x1']<=page.width+.1 and -.1<=c['top'] and c['bottom']<=page.height+.1 for c in chars),number
        extents.append(dict(page=number,left=min(c['x0'] for c in chars),right=max(c['x1'] for c in chars),top=min(c['top'] for c in chars),bottom=max(c['bottom'] for c in chars)))
result=dict(pages=len(reader.pages),abstract_characters=len(abstract),abstract_identical_on_all_six_surfaces=True,
            latex_warnings=0,bibtex_warnings=0,archived_hashes=len(archived),
            preserved_proof_files=len(baseline['proof_files']),preserved_original_check_files=len(baseline['check_files']),
            concept_doi=cff['doi'],deposition_metadata_has_doi=False,page_extents=extents)
(B/'artifact-checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='page_extents'},indent=2))
