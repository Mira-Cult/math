"""Offline, file-only replay of the published fixed-dimension proof controls."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile
r=Path(__file__).resolve().parent
for name,digest in json.loads((r/'SHA256SUMS.json').read_text()).items():
 assert hashlib.sha256((r/name).read_bytes()).hexdigest()==digest,name
with tempfile.TemporaryDirectory(prefix='prime-hyperk-') as temp:
 root=Path(temp); p=root/'problems/prime-arrays-beyond-square'
 shutil.copytree(r/'originals',p)
 commands=[
  [p/'code/hyperk_full.py','--self-test'],
  [p/'reviews/hyperk_uniform_frame_controls.py',root],
  [p/'reviews/hyperk_absorber_controls.py',root],
  [p/'reviews/hyperk_full_composition_controls.py','--source-root',p],
 ]
 for command in commands:
  print('RUN',command[0].name,flush=True)
  subprocess.run([sys.executable,'-B',*map(str,command)],check=True,cwd=root)
print('PASS: source hashes and four unmodified replay commands')
