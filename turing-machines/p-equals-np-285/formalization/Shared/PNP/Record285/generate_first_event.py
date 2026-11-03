"""Produce an untrusted certificate from the candidate entry to its first event.

Lean checks the entire silent prefix, endpoint tape, and marked transition.
"""
from pathlib import Path
from hashlib import sha256

HERE = Path(__file__).resolve().parent
raw = (HERE / 'events.tm').read_bytes()
if sha256(raw).hexdigest() != '1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7':
    raise ValueError('unexpected selected table')
rows = {}
for line in raw.decode('ascii').splitlines():
    if line.startswith('#'):
        continue
    q,r,w,d,n,e = line.split()
    rows[int(q),int(r)] = (int(w),d,int(n),int(e))
pair = {(110,0,1):('leftPair','scan110'), (48,0,1):('leftPair','shift48'),
        (51,0,1):('leftPair','scan51'), (6,1,0):('rightPair','boot6'),
        (14,0,1):('rightPair','shift14'), (46,0,1):('rightPair','scan46')}
run = {(1,1):('leftRun','clear1'), (48,1):('leftRun','shift48'),
       (51,1):('leftRun','scan51'), (110,1):('leftRun','scan110'),
       (119,0):('leftRun','scan119'), (10,0):('rightRun','fill10'),
       (11,1):('rightRun','scan11'), (12,1):('rightRun','scan12'),
       (14,1):('rightRun','scan14'), (15,1):('rightRun','scan15'),
       (16,1):('rightRun','scan16'), (46,1):('rightRun','scan46'),
       (55,0):('rightRun','scan55'), (56,1):('rightRun','erase56'),
       (109,0):('rightRun','scan109')}
q,head,left,read,right = 284,-3818,6,0,4**1910*((4**1910-1)//3)
elapsed = 0
commands = []
checkpoints = [(q,head,left,read,right,elapsed)]


def step():
    global q,head,left,read,right,elapsed
    if elapsed >= 100000:
        raise ValueError('expected marked event not reached')
    w,d,n,e = rows[q,read]
    if e:
        raise ValueError('marked transition entered the silent prefix')
    if d == 'L':
        left,read,right = left//2,left%2,2*right+w
        head -= 1
    else:
        left,read,right = 2*left+w,right%2,right//2
        head += 1
    q = n
    elapsed += 1


while not (q == 121 and read == 1):
    w,d,n,e = rows[q,read]
    side = left if d == 'L' else right
    key = (q,read,side%2)
    if key in pair:
        cmd,kind = pair[key]
        oldq,oldread,adjacent,count = q,read,side%2,0
        while q == oldq and read == oldread and (left if d == 'L' else right)%2 == adjacent:
            step(); step(); count += 1
        commands.append(f'.old (.{cmd} .{kind} {count-1})')
    elif (q,read) == (36,1):
        count = 0
        while (q,read) == (36,1):
            step(); count += 1
        commands.append(f'.scan36 {count-1}')
    elif (q,read) in run:
        cmd,kind = run[q,read]
        oldq,oldread,count = q,read,0
        while q == oldq and read == oldread:
            step(); count += 1
        commands.append(f'.old (.{cmd} .{kind} {count-1})')
    else:
        step()
        commands.append('.old .single')
    if len(commands)%8 == 0:
        checkpoints.append((q,head,left,read,right,elapsed))
    if elapsed > 100000:
        raise ValueError('expected marked event not reached')
if len(commands)%8:
    checkpoints.append((q,head,left,read,right,elapsed))
if elapsed != 38267 or rows[q,read][3] != 1:
    raise ValueError('unexpected pre-event state')
blocks = [commands[i:i+8] for i in range(0,len(commands),8)]
durs = [checkpoints[i+1][5]-checkpoints[i][5] for i in range(len(blocks))]
out = ['import Shared.PNP.Record285.FirstEventChecker',
       'import Shared.PNP.Record285.InitializationComposition',
       'set_option maxRecDepth 16384', 'set_option maxHeartbeats 0',
       'set_option exponentiation.threshold 8192',
       'namespace Shared.PNP.Record285.FirstEventCertificate',
       'open Shared.PNP.Record285.FirstEventChecker Shared.PNP.Record285.PhysicalNumeric',
       'open Shared.PNP.Record285.BootstrapSweep Shared.PNP.Record285.InitializationComposition',
       'open Shared.PNP.Record285.BootstrapChecker (silent_compose)']
for i,(q,h,l,r,rr,t) in enumerate(checkpoints):
    out.append(f'def c{i} : Config 285 := ⟨⟨{q},by decide⟩,({h}:Int),{l},{str(bool(r)).lower()},{rr}⟩')
for i,block in enumerate(blocks):
    out.append(f'def b{i} : List Command := ['+','.join(block)+']')
for i,d in enumerate(durs):
    out.append(f'theorem h{i} : verify b{i} c{i} = some ({d},c{i+1}) := by decide')
out += [f'theorem start_shape : c0 = candidate := by decide',
        f'theorem event_shape : c{len(blocks)}.state.val = 121 ∧ c{len(blocks)}.read = true := by decide', '',
        f'theorem silent_to_event : silent Record285.machine 38267 candidate = some c{len(blocks)} := by']
for i,d in enumerate(durs):
    out.append(f'  have step{i} : silent Record285.machine {d} c{i} = some c{i+1} := verify_sound b{i} c{i} c{i+1} {d} h{i}')
last = len(blocks)-1
out.append(f'  have tail{last} : silent Record285.machine {durs[last]} c{last} = some c{len(blocks)} := step{last}')
suffix = durs[last]
for i in range(last-1,-1,-1):
    previous = suffix
    suffix += durs[i]
    out.append(f'  have tail{i} : silent Record285.machine {suffix} c{i} = some c{len(blocks)} := silent_compose _ c{i} c{i+1} c{len(blocks)} {durs[i]} {previous} step{i} tail{i+1}')
out += ['  rw [← start_shape]', '  exact tail0', '',
        'end Shared.PNP.Record285.FirstEventCertificate']
(HERE / 'FirstEventCertificate.lean').write_text('\n'.join(out)+'\n',encoding='utf-8')
print(f'{len(commands)} commands, {len(blocks)} blocks, {elapsed} transitions')
