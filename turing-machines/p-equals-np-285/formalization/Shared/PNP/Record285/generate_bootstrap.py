"""Generate an untrusted, block-checked certificate for the first bootstrap.

The selected event table is read only after verifying its frozen SHA-256.
The resulting commands and checkpoints are verified by Lean's proved checker;
this script and its hash check are provenance, not a substitute for proof of
the literal text binding. Run from any directory with Python 3.11+.
"""
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
TABLE_HASH = '1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7'
BLOCK_SIZE = 64
raw = (HERE / 'events.tm').read_bytes()
if sha256(raw).hexdigest() != TABLE_HASH:
    raise ValueError('the selected event table does not match its frozen bytes')
rows = {}
for line in raw.decode('ascii').splitlines():
    if line.startswith('#'):
        continue
    q, read, write, direction, target, event = line.split()
    rows[int(q), int(read)] = (int(write), direction, int(target), int(event))

q, head, left, read, right, time = 0, 0, 0, 0, 0, 0
commands = []
checkpoints = [(q, head, left, read, right, time)]


def physical_step():
    global q, head, left, read, right, time
    write, direction, target, event = rows[q, read]
    if event != 0:
        raise ValueError('unexpected bootstrap event')
    if direction == 'L':
        left, read, right = left // 2, left % 2, 2 * right + write
        head -= 1
    elif direction == 'R':
        left, read, right = 2 * left + write, right % 2, right // 2
        head += 1
    else:
        raise ValueError('invalid movement')
    q = target
    time += 1


def append_command(code):
    commands.append(code)
    if len(commands) % BLOCK_SIZE == 0:
        checkpoints.append((q, head, left, read, right, time))


while q in (0, 2, 3, 4, 5):
    tag = {0: 1, 2: 2, 4: 3}.get(q)
    side = right if q == 4 else left
    if tag and read == 1 and side % 2 == 0:
        previous, pairs = q, 0
        while q == previous and read == 1 and (right if q == 4 else left) % 2 == 0:
            physical_step()
            physical_step()
            pairs += 1
        append_command(4 * (pairs - 1) + tag)
    else:
        physical_step()
        append_command(0)
if len(commands) % BLOCK_SIZE:
    checkpoints.append((q, head, left, read, right, time))
if (q, head, read, right, time) != (76, -2, 1, 30, 2133492):
    raise ValueError('unexpected bootstrap exit')
if left != (4**1910 - 1) // 3:
    raise ValueError('unexpected bootstrap tape')
blocks = [commands[i:i+BLOCK_SIZE] for i in range(0, len(commands), BLOCK_SIZE)]
if len(checkpoints) != len(blocks)+1:
    raise ValueError('invalid checkpoint count')
durations = [checkpoints[i+1][5]-checkpoints[i][5] for i in range(len(blocks))]

data = [
    'import Shared.PNP.Record285.BootstrapChecker', '',
    '/-! Generated from the frozen event table by `generate_bootstrap.py`.',
    'Each block is checked by the proved Lean certificate checker. -/',
    'namespace Shared.PNP.Record285.BootstrapTraceData',
    'open Shared.PNP.Record285.PhysicalNumeric',
]
for i, (state, pos, lnum, bit, rnum, _) in enumerate(checkpoints):
    data.append(f'def c{i} : Config 285 := ⟨⟨{state},by decide⟩,({pos} : Int),'
                f'{lnum},{str(bool(bit)).lower()},{rnum}⟩')
for i, block in enumerate(blocks):
    data.append(f'def b{i} : List Nat := [{",".join(map(str,block))}]')
data.append('end Shared.PNP.Record285.BootstrapTraceData')
(HERE / 'BootstrapTraceData.lean').write_text('\n'.join(data)+'\n', encoding='utf-8')

proof = [
    'import Shared.PNP.Record285.BootstrapTraceData', '',
    '/-! Kernel-checked bootstrap certificate. The literal text-to-numeric',
    'binding remains an explicit separate premise. -/',
    'set_option maxRecDepth 16384', 'set_option maxHeartbeats 0',
    'set_option exponentiation.threshold 4096',
    'namespace Shared.PNP.Record285.BootstrapTraceProof',
    'open Shared.Beeping Shared.Beeping.Machines',
    'open Shared.PNP.Record285.PhysicalNumeric',
    'open Shared.PNP.Record285.BootstrapRows',
    'open Shared.PNP.Record285.BootstrapSweep',
    'open Shared.PNP.Record285.BootstrapChecker',
    'open Shared.PNP.Record285.BootstrapTraceData', '',
]
for i, duration in enumerate(durations):
    proof.append(f'theorem block{i} : verify b{i} c{i} = some ({duration},c{i+1}) := by decide')
proof += [
    '',
    f'theorem final_shape : c{len(blocks)} = ⟨exit,(-2 : Int),rep4 1910,true,30⟩ := by decide',
    '',
    '/-- The entire first bootstrap is checked for any machine satisfying the ten rows. -/',
    'theorem bootstrap (M : Machine 285) (rows : Rows M) :',
    f'    silent M {time} c0 = some c{len(blocks)} := by',
]
for i, duration in enumerate(durations):
    proof.append(f'  have h{i} : silent M {duration} c{i} = some c{i+1} := '
                 f'verify_sound M rows b{i} c{i} c{i+1} {duration} block{i}')
last = len(blocks)-1
proof.append(f'  have tail{last} : silent M {durations[last]} c{last} = some c{len(blocks)} := h{last}')
sum_time = durations[last]
for i in range(last-1, -1, -1):
    previous = sum_time
    sum_time += durations[i]
    proof.append(f'  have tail{i} : silent M {sum_time} c{i} = some c{len(blocks)} := '
                 f'silent_compose M c{i} c{i+1} c{len(blocks)} {durations[i]} {previous} h{i} tail{i+1}')
proof += [
    '  exact tail0', '',
    '/-- Exact numeric endpoint of the first blank-start bootstrap. -/',
    'theorem bootstrap_shape (M : Machine 285) (rows : Rows M) :',
    f'    silent M {time} ⟨A,0,0,false,0⟩ = some ⟨exit,(-2 : Int),rep4 1910,true,30⟩ := by',
    '  have h := bootstrap M rows',
    '  rw [final_shape] at h',
    '  exact h', '',
    'end Shared.PNP.Record285.BootstrapTraceProof',
]
(HERE / 'BootstrapTraceProof.lean').write_text('\n'.join(proof)+'\n', encoding='utf-8')
print(f'{len(commands)} commands, {len(blocks)} blocks, {time} physical transitions')
