"""Run four finite suites with one numerical thread; --record archives their outputs."""
from pathlib import Path
import os,sys,subprocess,json,time,shutil
HERE=Path(__file__).resolve().parent
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','NUMEXPR_MAX_THREADS','VECLIB_MAXIMUM_THREADS','BLIS_NUM_THREADS'):os.environ[key]='1'
os.environ['PYTHONDONTWRITEBYTECODE']='1';records=[]
for script,out in [('check_sharp_ceiling.py','sharp_ceiling.json'),('check_hash_barrier.py','hash_barrier.json'),('independent_ceiling_checks.py','independent_ceiling_checks.json'),('independent_groups_checks.py','independent_groups_checks.json')]:
 start=time.monotonic();args=[sys.executable,'-X','utf8','-B',str(HERE/script)]
 if script.startswith('check_'):args.append(str(HERE/out))
 log=HERE/Path(script).with_suffix('.log')
 with log.open('w',encoding='utf-8',newline='\n') as stream:r=subprocess.run(args,cwd=HERE,stdout=stream,stderr=subprocess.STDOUT,timeout=10800)
 records.append({'script':script,'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3)})
 print(script,'PASS' if r.returncode==0 else 'FAIL',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 if '--record' in sys.argv:
  for p in (log,HERE/out):shutil.copy2(p,HERE/'recorded'/p.name)
(HERE/'run-results.json').write_text(json.dumps(records,indent=2)+'\n')
print('All four finite frontier suites passed',flush=True)
