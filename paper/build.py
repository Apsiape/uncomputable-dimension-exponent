"""Build with four plain pdflatex passes and BibTeX; keep intermediate files outside the release tree."""
from pathlib import Path
import argparse,os,re,shutil,subprocess,tempfile
HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--build-dir',type=Path,help='intermediate directory outside the source tree; default: a fresh temporary directory')
args=parser.parse_args()
OUT=args.build_dir or Path(tempfile.mkdtemp(prefix='uncomputable-price-build-'))
assert not OUT.resolve().is_relative_to(HERE.parent.resolve())
OUT.mkdir(parents=True,exist_ok=True)
for p in OUT.iterdir():
 if p.is_file() and p.suffix in {'.aux','.bbl','.blg','.log','.out','.toc','.pdf','.fls'}:p.unlink()
ENV={**os.environ,'SOURCE_DATE_EPOCH':'1793142000','FORCE_SOURCE_DATE':'1'}
for name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS','BLIS_NUM_THREADS'):ENV[name]='1'
def run(command,cwd=HERE,env=ENV):
 result=subprocess.run(command,cwd=cwd,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=900)
 if result.returncode:
  print(result.stdout[-7000:]);raise SystemExit('Manuscript compilation failed')
latex=['pdflatex','-no-shell-escape','-recorder','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(OUT),'main.tex']
run(latex)
run(['bibtex','main'],OUT,{**ENV,'BIBINPUTS':str(HERE)+os.pathsep})
shutil.copy2(OUT/'main.bbl',HERE/'main.bbl')
for _ in range(3):run(latex)
issues=[]
for line in (OUT/'main.log').read_text(errors='replace').splitlines():
 if re.search(r'pdfTeX warning|(?:LaTeX(?: Font)?|Package .+|Class .+) Warning:|undefined|Overfull|Underfull|multiply defined|Rerun to get|Float too large|ignored error|Missing character|^!',line,re.I):issues.append(line)
issues += [s for s in (OUT/'main.blg').read_text(errors='replace').splitlines() if 'Warning--' in s or 'error message' in s]
if issues:print('\n'.join(issues));raise SystemExit('Unresolved strict build issues')
shutil.copy2(OUT/'main.pdf',HERE/'main.pdf');shutil.copy2(OUT/'main.bbl',HERE/'main.bbl')
print('Four pdflatex passes and BibTeX passed; final PDF and BBL copied to paper/.')
print('Intermediate directory:',OUT.resolve())
