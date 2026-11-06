"""No-search replay of a contextual quotient and its supplied invariant.

This verifier uses the separately implemented tuple-path primitive interpreter,
not the producer's string-path graph, fixed-point search, or partition routine.
It checks a post-fixed point; leastness or producer optimality is unnecessary.
"""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'shared'))
from build_baseline import canonicalize
from test_occurrences import paths, return_path, continue_path
from test_natural import TreeVM


def check(builder,raw,new,names,certificate):
    from contextual_quotient import machine_digest,grammar_digest
    if certificate.get('schema') != 'horn-contextual-quotient-v1': raise ValueError('certificate schema')
    if certificate.get('domain') != 'zero-register source entry reached by the separately checked blank bootstrap':
        raise ValueError('certificate domain relabeling')
    if certificate.get('event_scope') != 'B colors and literal transition times preserved on the admitted blank run':
        raise ValueError('certificate event-scope relabeling')
    if certificate.get('abstract_domain') != {'1':'zero','2':'one','4':'at least two','union':'bitwise OR','unreachable':None}:
        raise ValueError('abstract-domain labeling')
    actual_raw,actual_names=canonicalize(builder)
    if (actual_raw.start,actual_raw.beep,actual_raw.rows,actual_names) != (raw.start,raw.beep,raw.rows,names):
        raise ValueError('table/builder binding')
    for field,value in [('grammar_sha256',grammar_digest(builder)),
                        ('raw_table_sha256',machine_digest(raw)),('table_sha256',machine_digest(new))]:
        if certificate.get(field) != value: raise ValueError(field)
    # Bind every abstract grammar edge to its actual emitted physical row.
    # Matching hashes alone cannot justify an unrelated grammar supplied by a caller.
    for index in builder.reachable():
        sequence=builder.sequences[index]
        if len(sequence.seq) != 2: raise ValueError('nonbinary grammar')
        for bit,child in enumerate(sequence.seq):
            if type(child) is int:
                expected=(bit,1,names[builder.sequences[child].name])
            elif child.startswith('_break.'):
                level=int(child.split('.')[1])
                if level < 0: raise ValueError('negative break depth')
                if bit == 0 and level == 0: expected=(1,-1,names['6.continue.0'])
                else: expected=(0,-1,names[f'6.break.{level-(bit == 0)}'])
            elif child.startswith('_continue.'):
                level=int(child.split('.')[1])-bit
                if level < 0: raise ValueError('negative continue depth')
                expected=(0,-1,names[f'6.continue.{level}'])
            elif child == 'beep' or child.startswith('3.'):
                expected=(bit,1,names[child])
            else: raise ValueError('unsupported grammar leaf')
            if raw.rows[names[sequence.name],bit] != expected:
                raise ValueError('grammar/physical row mismatch')
    occurrences=list(paths(builder))
    path_indices={path:i for i,(path,leaf,parent) in enumerate(occurrences)}
    if len(path_indices) != len(occurrences): raise ValueError('duplicate occurrence')
    registers=tuple(builder.registers)
    register_indices={str(register):i for i,register in enumerate(registers)}
    states=certificate.get('states_at_occurrences')
    if not isinstance(states,list) or len(states) != len(occurrences): raise ValueError('abstract inventory')
    parsed=[]
    for state in states:
        if state is None: parsed.append(None)
        elif type(state) is str and len(state) == len(registers) and all(c in '1234567' for c in state):
            parsed.append(tuple(map(int,state)))
        else: raise ValueError('bad abstract state')
    vm=TreeVM(builder)
    def resolve(path):
        leaf,canonical=vm.resolve(path)
        index=path_indices[canonical]
        if str(occurrences[index][1]) != str(leaf): raise ValueError('path interpretation disagrees')
        return index
    initial=parsed[resolve((1,1,0))]
    if initial is None or any(not(mask & 1) for mask in initial): raise ValueError('missing zero-register entry')
    edge_count=0
    for i,(path,leaf,parent) in enumerate(occurrences):
        state=parsed[i]
        if state is None: continue
        op=str(leaf)
        successors=[]
        if op.startswith('_break.'):
            successors.append((return_path(path,int(op.split('.')[1])),state))
        elif op.startswith('_continue.'):
            successors.append((continue_path(path,int(op.split('.')[1])),state))
        elif op == 'beep': successors.append((return_path(path,0),state))
        elif op.startswith('3.'):
            register,operation=op[2:].rsplit('.',1)
            if register not in register_indices: raise ValueError('unknown register')
            slot=register_indices[register]
            # Representatives 2 and 3 cover both decrement images of the >=2 class.
            values=[value for value,mask in ((0,1),(1,2),(2,4),(3,4)) if state[slot] & mask]
            images={}
            for value in values:
                if operation == 'inc': destination=return_path(path,0);result=value+1
                elif operation == 'decnz': destination=return_path(path,int(value == 0));result=max(0,value-1)
                else: raise ValueError('unsupported primitive')
                mask=1 if result == 0 else 2 if result == 1 else 4
                images[destination]=images.get(destination,0)|mask
            for destination,mask in images.items():
                image=list(state);image[slot]=mask
                successors.append((destination,image))
        else: raise ValueError('unsupported primitive')
        for destination,image in successors:
            target=parsed[resolve(destination)]
            if target is None or any(value & ~bound for value,bound in zip(image,target)):
                raise ValueError('invariant not closed at occurrence '+str(i))
            edge_count+=1
    # Every traversed grammar row is on a prefix of some reached primitive path.
    live_rows=set()
    root=builder.find_seq('main().0')
    for i,(path,leaf,parent) in enumerate(occurrences):
        if parsed[i] is None: continue
        node=root
        for bit in path[3:]:
            live_rows.add((names[builder.sequences[node].name],bit))
            node=builder.sequences[node].seq[bit]
    grammar_rows={(names[builder.sequences[node].name],bit) for node in builder.reachable() for bit in (0,1)}
    ignored=grammar_rows-live_rows
    if certificate.get('ignored_grammar_rows') != [list(key) for key in sorted(ignored)]:
        raise ValueError('ignored grammar row set')
    reached={raw.start};pending=[raw.start]
    while pending:
        q=pending.pop()
        for bit in (0,1):
            if (q,bit) in ignored: continue
            target=raw.rows[q,bit][2]
            if target not in reached: reached.add(target);pending.append(target)
    ignored|={(q,bit) for q in range(raw.count) if q not in reached for bit in (0,1)}
    if certificate.get('ignored_rows') != [list(key) for key in sorted(ignored)]: raise ValueError('ignored physical row set')
    raw_mapping=certificate.get('mapping')
    if not isinstance(raw_mapping,dict): raise ValueError('mapping format')
    try: mapping={int(q):target for q,target in raw_mapping.items()}
    except (TypeError,ValueError): raise ValueError('mapping keys')
    if len(mapping) != len(raw_mapping) or set(mapping) != set(range(raw.count)): raise ValueError('mapping domain')
    if any(type(value) is not int for value in mapping.values()) or set(mapping.values()) != set(range(new.count)):
        raise ValueError('mapping range')
    if mapping[raw.start] != new.start or mapping[raw.beep] != new.beep: raise ValueError('distinguished states')
    if set(new.rows) != {(q,b) for q in range(new.count) for b in (0,1)}: raise ValueError('non-total target')
    checked=0
    for q in range(raw.count):
        if (q == raw.beep) != (mapping[q] == new.beep): raise ValueError('event color')
        for bit in (0,1):
            write,move,target=new.rows[mapping[q],bit]
            if write not in (0,1) or move not in (-1,1) or target not in range(new.count): raise ValueError('malformed row')
            if (q,bit) not in ignored:
                old_write,old_move,old_target=raw.rows[q,bit]
                if (write,move,target) != (old_write,old_move,mapping[old_target]): raise ValueError('row simulation')
                checked+=1
    return {'abstract_occurrences':len(occurrences),'postfixed_edges_checked':edge_count,
            'physical_rows_checked':checked,'ignored_rows':len(ignored),'states':new.count,
            'scope':'conditional on source/runtime clean-configuration theorem and exact blank initialization'}
