"""Sequential source build and selected-proof comparator/kernel checks.
Requires Python 3.10+, Lean 4.35.0 and pinned dependency caches (lake exe cache get).
"""
from pathlib import Path
import argparse,os,sys,json,re,shutil,subprocess,time,hashlib,struct,ctypes
import ctypes.wintypes as w
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--dependency-root',type=Path,default=P/'.lake/packages')
ap.add_argument('--bin-dir',type=Path)
ap.add_argument('--build-only',action='store_true')
ap.add_argument('--plan-only',action='store_true')
ap.add_argument('--reuse-build',action='store_true',help='reuse local objects; no fresh-source-build claim')
a=ap.parse_args()
mods={f.relative_to(P).with_suffix('').as_posix().replace('/','.'):f for d in ['E2','Companion','QIT'] for f in (P/d).rglob('*.lean')}
mods.update({f.stem:f for f in P.glob('*.lean') if f.name!='lakefile.lean'})
order=[];seen=set();active=set()
def visit(n):
 if n in seen or n not in mods:return
 if n in active:raise RuntimeError('import cycle at '+n)
 active.add(n)
 for line in re.findall(r'(?m)^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',mods[n].read_text(encoding='utf-8-sig')):
  for dep in line.split('--')[0].split():visit(dep)
 active.remove(n);seen.add(n);order.append(n)
for root in json.loads((P/'BUILD-ROOTS.json').read_text()):visit(root)
if a.plan_only:
 print(json.dumps({'modules':len(order),'order':order},indent=2));sys.exit(0)
R=P/'.replay';R.mkdir(exist_ok=True)
if os.name=='nt':
 class Basic(ctypes.Structure):
     _fields_=[('PerProcessUserTimeLimit',ctypes.c_int64),('PerJobUserTimeLimit',ctypes.c_int64),('LimitFlags',w.DWORD),('MinimumWorkingSetSize',ctypes.c_size_t),('MaximumWorkingSetSize',ctypes.c_size_t),('ActiveProcessLimit',w.DWORD),('Affinity',ctypes.c_size_t),('PriorityClass',w.DWORD),('SchedulingClass',w.DWORD)]
 class IO(ctypes.Structure):
     _fields_=[(n,ctypes.c_uint64) for n in ('ReadOperationCount','WriteOperationCount','OtherOperationCount','ReadTransferCount','WriteTransferCount','OtherTransferCount')]
 class Extended(ctypes.Structure):
     _fields_=[('BasicLimitInformation',Basic),('IoInfo',IO),('ProcessMemoryLimit',ctypes.c_size_t),('JobMemoryLimit',ctypes.c_size_t),('PeakProcessMemoryUsed',ctypes.c_size_t),('PeakJobMemoryUsed',ctypes.c_size_t)]
 k=ctypes.WinDLL('kernel32',use_last_error=True)
 k.CreateJobObjectW.argtypes=[ctypes.c_void_p,w.LPCWSTR];k.CreateJobObjectW.restype=w.HANDLE
 k.SetInformationJobObject.argtypes=[w.HANDLE,ctypes.c_int,ctypes.c_void_p,w.DWORD];k.SetInformationJobObject.restype=w.BOOL
 k.AssignProcessToJobObject.argtypes=[w.HANDLE,w.HANDLE];k.AssignProcessToJobObject.restype=w.BOOL
 k.GetCurrentProcess.restype=w.HANDLE
 k.QueryInformationJobObject.argtypes=[w.HANDLE,ctypes.c_int,ctypes.c_void_p,w.DWORD,ctypes.c_void_p];k.QueryInformationJobObject.restype=w.BOOL
 job=k.CreateJobObjectW(None,None);lim=Extended();lim.BasicLimitInformation.LimitFlags=0x200;lim.JobMemoryLimit=10_000_000_000
 if not job or not k.SetInformationJobObject(job,9,ctypes.byref(lim),ctypes.sizeof(lim)) or not k.AssignProcessToJobObject(job,k.GetCurrentProcess()):raise ctypes.WinError(ctypes.get_last_error())
else:
 import resource
 resource.setrlimit(resource.RLIMIT_AS,(10_000_000_000,10_000_000_000))
env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env['LEAN_ABORT_ON_PANIC']='1'
if a.bin_dir:env['PATH']=str(a.bin_dir.resolve())+os.pathsep+env.get('PATH','')
else:
 lean_cmd=shutil.which('lean',path=env.get('PATH'))
 if not lean_cmd:raise RuntimeError('Install the pinned Lean toolchain first')
 prefix=subprocess.check_output([lean_cmd,'--print-prefix'],cwd=P,env=env,text=True).strip()
 env['PATH']=str(Path(prefix)/'bin')+os.pathsep+env.get('PATH','')
version=subprocess.check_output([shutil.which('lean',path=env.get('PATH')),'--version'],cwd=P,env=env,text=True)
if not re.search(r'\b4\.35\.0\b',version):raise RuntimeError('Expected Lean 4.35.0; got '+version)
for key in ['TEMP','TMP','MATHLIB_CACHE_DIR','LAKE_CACHE_DIR']:
 p=R/key.lower();p.mkdir(exist_ok=True);env[key]=str(p)
packages=[p for p in a.dependency_root.resolve().iterdir() if p.is_dir() and (p/'.lake/build/lib/lean').is_dir()]
if not any(p.name=='mathlib' for p in packages):raise RuntimeError('Missing Mathlib cache: run lake exe cache get first')
env['LEAN_PATH']=os.pathsep.join(str(p/'.lake/build/lib/lean') for p in [P]+packages)
if os.name=='nt':
 unix=Path(os.environ.get('ProgramFiles',''))/'Git/usr/bin'
 if (unix/'which.exe').exists():env['PATH']=env.get('PATH','')+os.pathsep+str(unix)
def exe(n):
 p=shutil.which(n,path=env.get('PATH'))
 if not p:raise RuntimeError('Missing '+n+' in PATH')
 return p
records=[]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(2**20),b''):h.update(chunk)
 return h.hexdigest()
def run(label,args,output=None,required=True):
 args=list(map(str,args));print(label,flush=True);start=time.monotonic()
 with (R/(label+'.log')).open('wb') as err:
  out=output.open('wb') if output else err
  try:rc=subprocess.run(args,cwd=P,env=env,stdin=subprocess.DEVNULL,stdout=out,stderr=err).returncode
  finally:
   if output:out.close()
 row={'label':label,'command':args,'exit':rc,'seconds':round(time.monotonic()-start,3)}
 if output:row.update(bytes=output.stat().st_size,sha256=sha(output))
 records.append(row);(R/'records.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
 if rc and required:raise RuntimeError(label+' failed; inspect '+str(R/(label+'.log')))
 return rc
if not a.reuse_build:
 for n in order:
  rel=mods[n].relative_to(P);out=P/'.lake/build/lib/lean'/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  run('build-'+n,[exe('lean'),'-j1','-M6144','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-DautoImplicit=false','-o',out,rel])
if a.build_only:sys.exit(0)
targets=re.findall(r'(?m)^#print axioms (\S+)',(P/'Audit.lean').read_text())
primitives=['Quot','Quot.mk','Quot.lift','Quot.ind','propext','Classical.choice','Quot.sound','Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod','Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight','String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char','optParam','autoParam','semiOutParam','outParam']
c=R/'challenge.ndjson';s=R/'solution.ndjson'
run('export-challenge',[exe('leanexport'),'Challenge','--','E2.challenge']+primitives,c)
run('export-solution',[exe('leanexport'),'Audit','--']+targets+primitives,s)
cmd=[exe('lake'),'comparator','--config','comparator.json','--challenge-from-export',c,'--solution-from-export',s]
if os.name=='nt':
 print('Windows: trusted local exports; Linux namespace sandbox unavailable.',flush=True)
 cmd+=['--inadvisably-no-sandbox']
run('comparator',cmd)
run('leanchecker',[exe('leanchecker'),'--silent','--from-export',s])
nanoda=Path(exe('nanoda_bin'))
if os.name=='nt':
 # Reserve 128 MiB of stack, without changing executable code or initial commit.
 data=bytearray(nanoda.read_bytes());assert data[:2]==b'MZ'
 pe=struct.unpack_from('<I',data,0x3c)[0];opt=pe+24
 assert data[pe:pe+4]==b'PE\0\0' and struct.unpack_from('<H',data,opt)[0]==0x20b
 old=struct.unpack_from('<Q',data,opt+72)[0]
 struct.pack_into('<Q',data,opt+72,134217728)
 patched=R/'nanoda-stack128.exe';patched.write_bytes(data)
 (R/'nanoda-stack-adjustment.json').write_text(json.dumps({'original_sha256':sha(nanoda),'copy_sha256':sha(patched),'file_offset':opt+72,'original_reserve':old,'new_reserve':134217728,'only_changed_field':'PE32+ SizeOfStackReserve'},indent=2),encoding='utf-8');nanoda=patched
cfg=R/'nanoda.json';cfg.write_text(json.dumps({'use_stdin':False,'export_file_path':str(s),'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'num_threads':1,'nat_extension':True,'string_extension':True},indent=2),encoding='utf-8')
run('nanoda',[nanoda,cfg]);print('Statement comparison and both replays passed.',flush=True)
