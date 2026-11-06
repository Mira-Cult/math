"""Injected whole-table selector/kernel fixtures for the new completion domain.

Expected tapes follow natural arithmetic and the reviewed paid unary block ABI.
These are labelled injected fixtures, not observations of actual blank startup.
No compiler or physical runtime generator is imported.
"""
from pathlib import Path
import argparse
import json
import random

from check_static import endpoint, sha, jd, completion
SEMANTIC_EXCLUSIONS=completion.EXCLUDED

def load(folder):
    return {p.name:json.loads(p.read_text()) for p in Path(folder).glob('*.json')}



def bank(anchor, values):
    result = {anchor}
    position = anchor+2
    for value in values:
        assert type(value) is int and value >= 0
        result.update(range(position,position+value+1))
        position += value+2
    return result


def grammar_occurrences(parent, selected):
    """Enter each unfolded grammar path through the literal root dispatcher.

    This binds the finite grammar, including every administrative leaf, to
    the physical control rows without importing the builder's sequence names.
    """
    pdata,sdata=load(parent),load(selected)
    names=pdata['names.json']; order=pdata['grammar.json']['registers']
    graph=endpoint.Graph(pdata['grammar.json'])
    _,raw=endpoint.table(parent/'raw.tm')
    _,completed=endpoint.table(selected/'raw.tm')
    _,companion=endpoint.table(selected/'machine.tm')
    _,marked=endpoint.table(selected/'events.tm')
    first=pdata['quotient.json']; second=sdata['quotient.json']; events=sdata['event-quotient.json']['mapping']
    forbidden={(names[name],z) for name,z in SEMANTIC_EXCLUSIONS.items()}
    anchor=max(len(path) for path,*_ in graph.leaves)+11
    cases,steps_total=0,0
    counts={name:0 for name in ('beep','inc','decnz','half','break','continue')}

    def return_path(path,skip):
        for i in range(len(path)-1,1,-1):
            if path[i] == 0:
                if skip: skip-=1
                else: return path[:i]+(1,)
        raise AssertionError('return outside root')

    def continue_path(path,skip):
        for i in range(len(path)-1,0,-1):
            if path[i] == 1:
                if skip: skip-=1
                else: return path[:i+1]
        raise AssertionError('continue outside root')

    for serial,(path,op,*_) in enumerate(graph.leaves):
        if op.startswith('3.'):
            kind,operand=endpoint.operand(op)
            values_to_test=(0,1,2,3,8,9) if kind=='half' else (0,1,4) if kind=='decnz' else (2,)
        else:
            kind=op if op=='beep' else op.split('.')[0][1:]
            values_to_test=(0,)
        for value in values_to_test:
            values=[(i+serial)%5 for i in range(len(order))]+[0,0,0]
            expected=list(values)
            if kind in ('inc','decnz','half'):
                index=order.index(operand); values[index]=expected[index]=value
                if kind=='inc': expected[index]+=1; outcome=0
                elif kind=='decnz':
                    expected[index]=max(0,value-1); outcome=int(value==0)
                    if value: expected.append(0)
                else:
                    expected[index]=value//2; outcome=int(value%2==0)
                    expected += [0]*((value+1)//2)
                target_path=return_path(path,outcome)
            elif kind=='beep': target_path=return_path(path,0)
            elif kind=='break': target_path=return_path(path,int(op.split('.')[1]))
            else:
                assert kind=='continue'
                target_path=continue_path(path,int(op.split('.')[1]))
            tape={i for i,b in enumerate(path) if b}|bank(anchor,values)
            q,head=names['main().0'],3
            beeps=marks=0
            for used in range(1_000_000):
                if q==names['4.dispatch.scan'] and head<0 and not any(
                    i in tape for i in range(max(len(path),len(target_path)),anchor)):
                    break
                z=int(head in tape)
                assert (q,z) not in forbidden
                w,d,t,e=raw[q,z]
                q1,t1=endpoint.mapped(first,q),endpoint.mapped(first,t)
                q2,t2=endpoint.mapped(second,q1),endpoint.mapped(second,t1)
                assert completed[q1,z]==(w,d,t1,e)
                assert companion[q2,z]==(w,d,t2,e)
                mark=int(t2==1)
                assert marked[endpoint.mapped(events,q2),z]==(w,d,endpoint.mapped(events,t2),mark)
                beeps+=e; marks+=mark
                if w: tape.add(head)
                else:tape.discard(head)
                head+=1 if d=='R' else -1; q=t
            else:raise AssertionError('grammar occurrence exceeded reviewer budget')
            expected_tape={i for i,b in enumerate(target_path) if b}|bank(anchor,expected)
            assert tape==expected_tape,(serial,op,value,sorted(tape^expected_tape))
            assert beeps==marks==int(kind=='beep')
            cases+=1;counts[kind]+=1;steps_total+=used
    return dict(unfolded_occurrences=len(graph.leaves),injected_cases=cases,
                physical_steps=steps_total,per_kind=counts,
                entry='actual main().0 control rows at head 3 with independently encoded 110 path',
                relation='Every primitive and lexical leaf has its independently expected whole tape, continuation, event count and selected state maps.')


def check(parent, selected):
    pdata, sdata = load(parent), load(selected)
    names = pdata['names.json']
    order = pdata['grammar.json']['registers']
    _, raw = endpoint.table(parent/'raw.tm')
    _, old = endpoint.table(parent/'machine.tm')
    _, completed = endpoint.table(selected/'raw.tm')
    _, companion = endpoint.table(selected/'machine.tm')
    _, marked = endpoint.table(selected/'events.tm')
    first_map, second_map = pdata['quotient.json'], sdata['quotient.json']
    event_map = sdata['event-quotient.json']['mapping']
    forbidden = {(names[name],bit) for name,bit in SEMANTIC_EXCLUSIONS.items()}
    forbidden |= {(names['silent.sink'],z) for z in (0,1)}
    all_visits, cases, transitions = set(), 0, 0
    kinds = dict(inc=0,decnz=0,half=0,preparation=0)
    cfg_hashes = []

    def run(q,head,tape,stops):
        nonlocal transitions
        tape = set(tape)
        for step in range(2_000_000):
            if q in stops:
                transitions += step
                return q,head,tape,step
            z = int(head in tape)
            assert (q,z) not in forbidden
            all_visits.add((q,z))
            w,d,t,event = raw[q,z]
            assert event == 0
            q1,t1 = endpoint.mapped(first_map,q),endpoint.mapped(first_map,t)
            q2,t2 = endpoint.mapped(second_map,q1),endpoint.mapped(second_map,t1)
            # Every observed paid segment is checked against both complete
            # B carriers and the marked quotient at the same physical step.
            assert old[q1,z] == completed[q1,z] == (w,d,t1,event)
            assert companion[q2,z] == (w,d,t2,event)
            assert marked[endpoint.mapped(event_map,q2),z] == (w,d,endpoint.mapped(event_map,t2),0)
            if w: tape.add(head)
            else: tape.discard(head)
            head += 1 if d == 'R' else -1
            q = t
        raise AssertionError('injected finite segment exceeded reviewer budget')

    rng = random.Random(0x3871031)
    stops = {names['6.break.0'],names['6.break.1']}
    operations = sorted(name for name in names if name.startswith('3.'))
    for operation in operations:
        kind,operand = endpoint.operand(operation)
        index = order.index(operand)
        for value in [0,1,2,3,4,5,6,7,8,9,15,16,17,31,32,33,63,64,127,128]:
            for gap in (3,17):
                h,anchor = -23,-23+gap
                values = [rng.randrange(18) for _ in order] + [0,0,0,0]
                values[index] = value
                prefix = {h-9,h-5,h-3,h-2}
                pad = 2 if kind == 'half' else 3
                tape = prefix | {h} | set(range(h+pad,anchor+1)) | bank(anchor,values)
                q,head,tape,steps = run(names[operation],h,tape,stops)
                expected = list(values)
                if kind == 'inc':
                    expected[index] += 1; outcome = 0
                elif kind == 'decnz':
                    expected[index] = max(0,value-1); outcome = int(value == 0)
                    if value: expected.append(0)
                else:
                    assert kind == 'half'
                    expected[index] //= 2; outcome = int(value % 2 == 0)
                    expected += [0]*((value+1)//2)
                assert q == names[f'6.break.{outcome}'] and head == h-1
                assert tape == prefix | set(range(h+2,anchor+1)) | bank(anchor,expected)
                cases += 1; kinds[kind] += 1
                if value in (0,1,128) and gap == 3:
                    cfg_hashes.append(jd([operation,value,q,head,sorted(tape),steps]))
    for name,pads in [('1b.reg.prep_1',2),('2h.native_half.prep',1),('shared.selector.bootstrap.prep',1)]:
        for gap in (3,7,29):
            h,anchor=-11,-11+gap
            values=[0,7,0,3,11,0]
            prefix={h-7,h-3,h-1}
            tape=prefix|{h}|bank(anchor,values)
            q,head,tape,steps=run(names[name],h+1,tape,{names['6.continue.0']})
            assert head == anchor-1
            assert tape == prefix|{h}|set(range(h+pads+1,anchor+1))|bank(anchor,values)
            cases += 1; kinds['preparation'] += 1
    for name,excluded in SEMANTIC_EXCLUSIONS.items():
        assert (names[name],1-excluded) in all_visits, ('allowed row not covered',name)
    return dict(format='np-conp-transfer-independent-domain-fixtures-v1',
                reviewer='internal-model-reviewer; nonauthor of selected source, lowerings and completion', source_sha256=pdata['metadata.json']['source_sha256'],
                checker_sha256=sha(Path(__file__)), helper_sha256=sha(Path(__file__).with_name('check_static.py')),
                injected_cases=cases, operations=len(operations), primitive_cases=kinds,
                literal_steps=transitions, largest_operand=128,
                constrained_states_covered=len(SEMANTIC_EXCLUSIONS), excluded_rows_taken=0,
                checkpoint_digest=jd(cfg_hashes),
                grammar_occurrences=grammar_occurrences(parent,selected),
                tables={label:{p.name:sha(p) for p in [folder/'raw.tm',folder/'machine.tm',folder/'events.tm']}
                        for label,folder in [('parent',parent),('selected',selected)]},
                scope='Injected finite whole-table paid preparation/selector/kernel segments, including whole tapes, both returns, exact appended zero reserves and composed state maps at every step. Actual blank startup and conventional all-natural domain proof are separate.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--parent',required=True,type=Path)
    parser.add_argument('--selected',required=True,type=Path)
    parser.add_argument('--out',required=True,type=Path)
    args=parser.parse_args()
    result=check(args.parent,args.selected)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))
