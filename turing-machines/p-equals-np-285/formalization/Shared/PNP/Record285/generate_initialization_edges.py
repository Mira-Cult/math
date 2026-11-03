"""Generate untrusted finite edge certificates around the repeated cycles.

The beginning reaches cycle 2; the end starts at cycle 1906 and reaches the
candidate source-entry control. Lean checks all rows, segments and full tapes.
"""
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
raw = (HERE / 'events.tm').read_bytes()
if sha256(raw).hexdigest() != '1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7':
    raise ValueError('unexpected selected table')
rows = {}
for line in raw.decode('ascii').splitlines():
    if line.startswith('#'):
        continue
    q,r,w,d,n,e=line.split()
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


def config(n):
    return (76,-2*(n+1),(4**(1910-n)-1)//3+1,0,
            4**(n+2)*((4**(n+2)-1)//3))


def generate(label, start, stop, target, duration):
    q,head,left,read,right = start
    elapsed = 0
    commands = []
    checkpoints = [(q,head,left,read,right,elapsed)]

    def step():
        nonlocal q,head,left,read,right,elapsed
        if elapsed >= 200000:
            raise ValueError('expected edge not reached')
        w,d,n,e = rows[q,read]
        if e:
            raise ValueError('unexpected marked event')
        if d == 'L':
            left,read,right = left//2,left%2,2*right+w
            head -= 1
        else:
            left,read,right = 2*left+w,right%2,right//2
            head += 1
        q = n
        elapsed += 1

    while not (elapsed and stop(q,head,left,read,right)):
        w,d,n,e = rows[q,read]
        side = left if d == 'L' else right
        key = (q,read,side%2)
        if key in pair:
            cmd,kind = pair[key]
            oldq,oldread,adjacent,count = q,read,side%2,0
            while q == oldq and read == oldread and (left if d == 'L' else right)%2 == adjacent:
                step(); step(); count += 1
            commands.append(f'.{cmd} .{kind} {count-1}')
        elif (q,read) in run:
            cmd,kind = run[q,read]
            oldq,oldread,count = q,read,0
            while q == oldq and read == oldread:
                step(); count += 1
            commands.append(f'.{cmd} .{kind} {count-1}')
        else:
            step()
            commands.append('.single')
        if len(commands)%8 == 0:
            checkpoints.append((q,head,left,read,right,elapsed))
        if elapsed > 200000:
            raise ValueError('expected edge not reached')
    if len(commands)%8:
        checkpoints.append((q,head,left,read,right,elapsed))
    if (q,head,left,read,right) != target or elapsed != duration:
        raise ValueError('unexpected edge configuration')
    blocks = [commands[i:i+8] for i in range(0,len(commands),8)]
    durs = [checkpoints[i+1][5]-checkpoints[i][5] for i in range(len(blocks))]
    out = ['import Shared.PNP.Record285.InitializationRounds',
           'set_option maxRecDepth 16384', 'set_option maxHeartbeats 0',
           'set_option exponentiation.threshold 8192',
           f'namespace Shared.PNP.Record285.InitializationEdge{label}',
           'open Shared.PNP.Record285.InitializationChecker Shared.PNP.Record285.PhysicalNumeric',
           'open Shared.PNP.Record285.BootstrapSweep Shared.PNP.Record285.BootstrapRows',
           'open Shared.PNP.Record285.InitializationRounds',
           'open Shared.PNP.Record285.BootstrapChecker (silent_compose)']
    for i,(q,h,l,r,rr,t) in enumerate(checkpoints):
        out.append(f'def c{i} : Config 285 := ⟨⟨{q},by decide⟩,({h}:Int),{l},{str(bool(r)).lower()},{rr}⟩')
    for i,block in enumerate(blocks):
        out.append(f'def b{i} : List Command := ['+','.join(block)+']')
    for i,d in enumerate(durs):
        out.append(f'theorem h{i} : verify b{i} c{i} = some ({d},c{i+1}) := by decide')
    start_expr = 'cfg 0' if label == 'Start' else 'cfg 1906'
    end_expr = 'cfg 2' if label == 'Start' else '⟨⟨284,by decide⟩,(-3818:Int),6,false,4^1910*rep4 1910⟩'
    out += [f'theorem start_shape : c0 = {start_expr} := by decide',
            f'theorem end_shape : c{len(blocks)} = {end_expr} := by decide', '',
            f'theorem edge : silent Record285.machine {duration} ({start_expr}) = some ({end_expr}) := by']
    for i,d in enumerate(durs):
        out.append(f'  have step{i} : silent Record285.machine {d} c{i} = some c{i+1} := verify_sound b{i} c{i} c{i+1} {d} h{i}')
    last = len(blocks)-1
    out.append(f'  have tail{last} : silent Record285.machine {durs[last]} c{last} = some c{len(blocks)} := step{last}')
    suffix = durs[last]
    for i in range(last-1,-1,-1):
        previous = suffix
        suffix += durs[i]
        out.append(f'  have tail{i} : silent Record285.machine {suffix} c{i} = some c{len(blocks)} := silent_compose _ c{i} c{i+1} c{len(blocks)} {durs[i]} {previous} step{i} tail{i+1}')
    out += ['  rw [← start_shape, ← end_shape]', '  exact tail0', '',
            f'end Shared.PNP.Record285.InitializationEdge{label}']
    (HERE / f'InitializationEdge{label}.lean').write_text('\n'.join(out)+'\n',encoding='utf-8')
    print(f'{label}: {len(commands)} commands, {len(blocks)} blocks, {elapsed} transitions')


generate('Start', config(0), lambda q,h,l,r,rr: (q,h,l,r,rr) == config(2), config(2), 61396)
expected_final = (284,-3818,6,0,4**1910*((4**1910-1)//3))
generate('End', config(1906), lambda q,h,l,r,rr: q == 284, expected_final, 122388)
