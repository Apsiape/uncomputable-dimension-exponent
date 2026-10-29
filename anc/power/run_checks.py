"""Replay the seven finite power-scale checks sequentially; recorded/ is unchanged."""
import os,sys,json,subprocess,time
from pathlib import Path
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS','BLIS_NUM_THREADS'):os.environ[key]='1'
os.environ['PYTHONDONTWRITEBYTECODE']='1'
HERE=Path(__file__).resolve().parent
CHECKS=('moments/attack_clock.py','moments/attack_moments_lamps.py','stopped/check_stopped_calibrator.py','rotation/check_rotation.py','stack/adversarial_checks.py','claims/check_scaled_machine.py','validation/independent_checks.py')
records=[]
for relative in CHECKS:
 path=HERE/relative;start=time.monotonic()
 with path.with_suffix('.log').open('w',encoding='utf-8',newline='\n') as output:
  result=subprocess.run([sys.executable,'-B',str(path)],cwd=path.parent,env=os.environ,stdout=output,stderr=subprocess.STDOUT,timeout=600)
 records.append({'script':relative,'exit_code':result.returncode,'seconds':round(time.monotonic()-start,3)})
 print(relative,'PASS' if result.returncode==0 else 'FAIL',flush=True)
 if result.returncode:raise SystemExit(result.returncode)
(HERE/'run-results.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print('All seven finite power-scale checks passed',flush=True)
