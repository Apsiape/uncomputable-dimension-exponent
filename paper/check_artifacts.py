"""Local editorial and PDF checks; read-only except paper/build/ QA artifacts."""
import os
import sys
sys.dont_write_bytecode = True
os.environ['OMP_NUM_THREADS'] = '1'
from pathlib import Path
import hashlib
import json
import re
from PIL import Image, ImageDraw
from pypdf import PdfReader
import pdfplumber
import yaml

P = Path(__file__).resolve().parent
R = P.parent
build = P/'build'
build.mkdir(exist_ok=True)
pages = sorted((build/'render').glob('page-*.png'))
assert pages
for start in range(0, len(pages), 12):
    sheet = Image.new('RGB', (3*350, 4*520), 'white')
    draw = ImageDraw.Draw(sheet)
    for pos, path in enumerate(pages[start:start+12]):
        pic = Image.open(path).convert('RGB')
        pic.thumbnail((330, 478))
        x, y = (pos%3)*350+10, (pos//3)*520+24
        sheet.paste(pic, (x,y))
        draw.text((x,y-19),f'Page {start+pos+1}',fill='black')
    sheet.save(build/f'contact-{start//12+1}.png')

reader = PdfReader(P/'main.pdf')
assert len(reader.pages) == len(pages)
text = '\n'.join(page.extract_text() or '' for page in reader.pages)
assert '??' not in text
MARKER = 'INDEPENDENT CHECKS: to be added'
assert MARKER not in text
abstract = (P/'abstract-arxiv.txt').read_text(encoding='utf-8').strip()
assert len(abstract) <= 1920
assert abstract in (R/'README.md').read_text(encoding='utf-8')
assert yaml.safe_load((R/'CITATION.cff').read_text(encoding='utf-8'))['abstract'] == abstract
assert json.loads((R/'.zenodo.json').read_text(encoding='utf-8'))['description'] == '<p>'+abstract+'</p>'
methods = (P/'sections/methods.tex').read_text()
anc_readme = (R/'anc/README.md').read_text()
assert MARKER not in methods
assert MARKER not in anc_readme
assert not any(MARKER in f.read_text(encoding='utf-8') for f in (P/'sections').glob('*.tex'))
assert not (R/'anc/independent').exists()
assert not (R/'anc/provenance').exists()
source = '\n'.join(f.read_text() for f in (P/'sections').glob('*.tex'))
assert not re.search(r'checked by us|by the authors',source,re.I)
log = (P/'main.log').read_text(errors='replace')
warnings = re.findall(r'(?m)^(?:LaTeX Warning|Package .* Warning|Overfull|Underfull).*$',log)
assert not warnings, warnings
assert not re.search(r'(?i)warning--|error message', (P/'main.blg').read_text())
cff = yaml.safe_load((R/'CITATION.cff').read_text())
zen = json.loads((R/'.zenodo.json').read_text())
assert [a['family-names'] for a in cff['authors']] == ['Douglas','Mghirbi']
assert [a['name'] for a in zen['creators']] == ['Douglas, Seth','Mghirbi, Nidhal']
assert 'doi' not in zen and 'doi' not in cff
assert all((R/name).is_file() for name in ['README.md','CITATION.cff','.zenodo.json','RIGHTS.md',
    'NOTICE','LICENSE-CC-BY-4.0.txt','LICENSE-MIT.txt','LICENSE-APACHE-2.0.txt'])
manifest = R/'anc/SHA256SUMS'
for line in manifest.read_text().splitlines():
    digest, rel = line.split('  ',1)
    assert hashlib.sha256((R/'anc'/rel).read_bytes()).hexdigest() == digest, rel

extents = []
with pdfplumber.open(P/'main.pdf') as pdf:
    for number,page in enumerate(pdf.pages,1):
        chars = [c for c in page.chars if c.get('text','').strip()]
        extents.append({'page':number,'left':min(c['x0'] for c in chars),
                        'right':max(c['x1'] for c in chars),
                        'top':min(c['top'] for c in chars),
                        'bottom':max(c['bottom'] for c in chars)})
        assert all(-.1<=c['x0'] and c['x1']<=page.width+.1
                   and -.1<=c['top'] and c['bottom']<=page.height+.1 for c in chars)
result={'pages':len(reader.pages),'abstract_characters':len(abstract),
        'latex_warnings':warnings,'bibtex_warnings':0,'open_check_markers':0,
        'abstract_identical':'abstract-arxiv.txt, README.md, CITATION.cff, .zenodo.json',
        'ancillary_hashes':'all match','metadata_authors':'Douglas, Mghirbi',
        'page_extents':extents}
(build/'artifact-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='page_extents'},indent=2))
