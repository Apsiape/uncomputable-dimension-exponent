"""Replay three finite profile suites sequentially with one numerical thread.
Generated JSON/logs are written beside scripts; --record refreshes archived outputs.
"""
from pathlib import Path
import os,sys,subprocess,json,time,shutil
HERE=Path(__file__).resolve().parent
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS','BLIS_NUM_THREADS'):os.environ[key]='1'
os.environ['PYTHONDONTWRITEBYTECODE']='1'
records=[]
for script,output in [('check_carry_checker.py','carry_checker.json'),('check_hold_stream.py','hold_stream.json'),('independent_checks.py','independent_checks.json')]:
 start=time.monotonic();log=HERE/Path(script).with_suffix('.log')
 with log.open('w',encoding='utf-8',newline='\n') as stream:result=subprocess.run([sys.executable,'-X','utf8','-B',str(HERE/script)],cwd=HERE,stdout=stream,stderr=subprocess.STDOUT,timeout=1800)
 records.append({'script':script,'exit_code':result.returncode,'seconds':round(time.monotonic()-start,3)})
 print(script,'PASS' if result.returncode==0 else 'FAIL',flush=True)
 if result.returncode:raise SystemExit(result.returncode)
 if '--record' in sys.argv:
  for p in (log,HERE/output):shutil.copy2(p,HERE/'recorded'/p.name)
(HERE/'run-results.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print('All three finite profile suites passed',flush=True)
