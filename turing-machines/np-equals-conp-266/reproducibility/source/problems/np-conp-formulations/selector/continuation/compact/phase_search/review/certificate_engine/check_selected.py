"""Nonauthor implementation checks for the normalized-prefix 387-state table.

The compiler, its analyzer, completion solver and rewriting code are not
imported.  The earlier independent tuple-path interpreter is reused explicitly;
CFG reconstruction, contextual contraction, storage, hole derivation, mutations
and composition checks below are new review code.
"""
from collections import defaultdict, deque
from copy import deepcopy
from pathlib import Path
import argparse
import ast
import hashlib
import importlib.util
import json
import subprocess

HERE = Path(__file__).resolve().parent
PHASE = HERE.parents[1]
COMPACT = PHASE.parent
ENDPOINT = COMPACT / 'tape_local/review/binary_kernel/check_endpoint.py'
ENDPOINT_SHA = 'dd4729fd95f39cdf3f60e313f68fd2a5a2ae70f1cc02294f87289a4bf193ba0c'
SOURCE = PHASE / 'coordinator/pair_normalize.py'
SOURCE_SHA = '7d98b2beb3676f7d0e4f0d6785a5a78d4817f05f23ec38c82635a3ea4b31a039'
SEMANTIC_EXCLUSIONS = {
    '1b.reg.prep_1': 1,
    '2h.native_half.begin': 0,
    '2h.native_half.boundary': 1,
    '2h.native_half.prep': 1,
    '2h.native_half.undo': 0,
    'shared.selector.bootstrap.prep': 1,
    'shared.selector.mark': 0,
    'shared.selector.mode0.pad1': 1,
    'shared.selector.mode0.pad2': 1,
    'shared.selector.mode1.pad1': 1,
    'shared.selector.mode1.pad2': 1,
    'shared.selector.prep': 1,
    'shared.selector.skip_separator': 1,
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def jd(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


assert sha(ENDPOINT) == ENDPOINT_SHA
spec = importlib.util.spec_from_file_location('earlier_independent_endpoint', ENDPOINT)
endpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(endpoint)


def load(folder):
    return {p.name: json.loads(p.read_text()) for p in Path(folder).glob('*.json')}


def runtime_inheritance(parent, data):
    """Compare literal named runtime rows with the exact inherited Git object."""
    control = COMPACT/'native/machines/selected'
    repo = next(p for p in HERE.parents if (p/'RESEARCH_PROTOCOL.md').is_file())
    producer = '07d12262fca4f4b12621b240122f978db8f32d57'
    for name in ('raw.tm','names.json'):
        path = control/name
        committed = subprocess.check_output(['git','-c','protocol.allow=never','show',
            producer+':'+path.relative_to(repo).as_posix()],cwd=repo)
        assert path.read_bytes() == committed
    assert sha(control/'raw.tm') == 'cbe5f4461f3d421c78b1f27301a29ea2c1a098a0982cd3244b97b02759842e4d'

    def named(folder,names):
        reverse = {q:name for name,q in names.items()}
        assert len(reverse) == len(names)
        return {(reverse[q],z):(w,d,reverse[t],e)
                for (q,z),(w,d,t,e) in endpoint.table(folder/'raw.tm')[1].items()}

    old_names = json.loads((control/'names.json').read_text())
    old = named(control,old_names)
    current = named(parent,data['names.json'])
    runtime_names = {name for name in data['names.json']
                     if not name.startswith(('compact_grammar_','main(', '3.'))}
    same = set(runtime_names) & set(old_names)
    for name in same:
        for bit in (0,1):
            assert current[name,bit] == old[name,bit], name
    added = runtime_names-set(old_names)
    assert added == {'2h.native_half.select.3'}
    assert current['2h.native_half.select.3',0] == (0,'R','2h.native_half.select.2',0)
    assert current['2h.native_half.select.3',1] == (1,'R','2h.native_half.select.3',0)
    order = data['grammar.json']['registers']
    natives = data['native-runtime.json']['operands']
    assert order[:len(natives)] == natives and len(natives) == 4
    leaves = {name for name in data['names.json'] if name.startswith('3.')}
    for op in leaves:
        kind,operand = endpoint.operand(op)
        if kind == 'half':
            index = natives.index(operand)
            assert current[op,0] == (1,'R','2h.native_half.prep',0)
            assert current[op,1] == (0,'R',f'2h.native_half.select.{index}',0)
        else:
            index = order.index(operand)
            assert current[op,0] == (1,'R','1b.reg.prep_1',0)
            assert current[op,1] == (int(kind == 'decnz'),'R',f'shared.selector.select.{index+1}',0)
    paths = [path for path,*_ in endpoint.Graph(data['grammar.json']).leaves]
    maximum = max(map(len,paths))
    assert maximum == data['selector.json']['max_leaf_path'] < 3822
    assert len(order) == data['selector.json']['registers'] <= 1909
    for filename,digest in data['metadata.json']['native_producers'].items():
        assert sha(COMPACT/'compiler/native'/filename) == digest
    for filename,digest in data['metadata.json']['selected_producers'].items():
        assert sha(PHASE/filename) == digest
    return dict(inherited_git_producer=producer, exact_common_runtime_rows=2*len(same),
                newly_counted_runtime_rows=2*len(added), checked_primitive_entries=len(leaves),
                native_operands=natives, maximum_control_path=maximum,
                paid_initial_register_capacity=1909)


def core(graph, zero_rows=frozenset(), rename=None):
    """Erase only finite administrative paths and proven zero/no-op tests."""
    zero_rows = set(map(tuple, zero_rows))

    def forward(position):
        seen = set()
        while True:
            op, *targets = graph.rows[position]
            is_zero = tuple(graph.leaves[position][2:]) in zero_rows
            if not is_zero and not op.startswith(('_break.', '_continue.')):
                return position
            assert position not in seen, 'silent administrative cycle'
            seen.add(position)
            if is_zero:
                assert endpoint.operand(op)[0] in ('decnz', 'half')
                position = targets[1]
            else:
                position = targets[0]

    # Checking unreachable occurrences too is a conservative finite-progress
    # check; no removed control segment is accepted merely because unsampled.
    for position in range(len(graph.rows)):
        forward(position)
    entry = forward(graph.entry)
    ids, work, rows = {entry: 0}, deque([entry]), []
    while work:
        position = work.popleft()
        op, *targets = graph.rows[position]
        targets = [forward(target) for target in targets]
        for target in targets:
            if target not in ids:
                ids[target] = len(ids)
                work.append(target)
        if rename is not None:
            op = endpoint.renamed(op, rename)
        rows.append([op, *[ids[target] for target in targets]])
    return dict(entry=0, rows=rows)


def source_cfg(source, allocation):
    """Reconstruct source CFG edges/read sets independently from the AST."""
    tree = ast.parse(source.read_text())
    functions = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}
    assert set(functions) == set(allocation['functions'])
    totals = {}
    for name, function in functions.items():
        record = allocation['functions'][name]
        variables = set(record['colours'])
        returns = record['returns']
        assert record['parameters'] == [arg.arg for arg in function.args.args]

        def reads(expr):
            return {n.id for n in ast.walk(expr) if isinstance(n, ast.Name)
                    and isinstance(n.ctx, ast.Load) and n.id in variables}

        def writes(expr):
            return {n.id for n in ast.walk(expr) if isinstance(n, ast.Name)}

        exit_key = ('exit', 0)
        expected = {exit_key: (set(), set(returns), [])}

        def block(statements, following, break_to=None):
            for stmt in reversed(statements):
                if isinstance(stmt, ast.While):
                    key = ('while', stmt.lineno)
                    after_else = block(stmt.orelse, following, break_to)
                    body = block(stmt.body, key, following)
                    expected[key] = (set(), reads(stmt.test), [body, after_else])
                elif isinstance(stmt, ast.If):
                    key = ('if', stmt.lineno)
                    yes = block(stmt.body, following, break_to)
                    no = block(stmt.orelse, following, break_to)
                    expected[key] = (set(), reads(stmt.test), [yes, no])
                elif isinstance(stmt, ast.Assign):
                    key = ('assign', stmt.lineno)
                    definitions = set().union(*(writes(t) for t in stmt.targets))
                    expected[key] = (definitions, reads(stmt.value), [following])
                elif isinstance(stmt, ast.AugAssign):
                    key = ('augment', stmt.lineno)
                    definitions = writes(stmt.target)
                    expected[key] = (definitions, reads(stmt.value) | definitions, [following])
                elif isinstance(stmt, ast.Return):
                    key = ('return', stmt.lineno)
                    expected[key] = (set(returns), reads(stmt.value), [exit_key])
                elif isinstance(stmt, ast.Break):
                    assert break_to is not None
                    key = ('break', stmt.lineno)
                    expected[key] = (set(), set(), [break_to])
                else:
                    assert isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
                    assert isinstance(stmt.value.func, ast.Name) and stmt.value.func.id == 'beep'
                    key = ('beep', stmt.lineno)
                    expected[key] = (set(), set(), [following])
                assert key != exit_key
                following = key
            return following

        entry = block(function.body, exit_key)
        cfg = record['cfg']
        supplied = cfg['nodes']
        keys = [(n['kind'], n['line']) for n in supplied]
        assert len(keys) == len(set(keys)) and set(keys) == set(expected)
        assert keys[cfg['entry']] == entry and keys[cfg['exit']] == exit_key
        for key, node in zip(keys, supplied):
            definitions, uses, targets = expected[key]
            assert set(node['defines']) == definitions and set(node['uses']) == uses
            assert [keys[t] for t in node['successors']] == targets
            outgoing = set().union(*(set(supplied[t]['live_in']) for t in node['successors']))
            assert set(node['live_out']) == outgoing
            assert set(node['live_in']) == uses | (outgoing - definitions)
            # Values needed simultaneously, simultaneous destinations, and
            # every newly defined value versus surviving values are separate.
            required = [set(node['live_in']), outgoing, definitions,
                        definitions | outgoing]
            for names in required:
                assert len({record['colours'][v] for v in names}) == len(names)
        for variable, neighbours in record['graph'].items():
            assert variable in variables
            for neighbour in neighbours:
                assert variable in record['graph'][neighbour]
                assert record['colours'][variable] != record['colours'][neighbour]
        height = allocation['heights'][name]
        for variable, colour in record['colours'].items():
            assert allocation['mapping'][name+'.'+variable] == f'$liveframe.{height}.{colour}'
        for node in ast.walk(function):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                assert allocation['heights'][node.func.id] < height
        totals[name] = dict(nodes=len(keys), variables=len(variables),
                            frame_size=allocation['frame_sizes'][name])
    original = ast.parse((COMPACT/'source/certificate_popfirst_power.py').read_text())
    old_accept = next(n for n in original.body if isinstance(n, ast.FunctionDef) and n.name == 'accept')
    assert ast.dump(functions['accept'], include_attributes=False) == ast.dump(old_accept, include_attributes=False)
    return totals


def storage(data):
    context = data['contextual-tree-certificate.json']
    original = context['input_grammar']
    pre = data['pre-control-grammar.json']
    contracted = data['pre-projection-grammar.json']
    projected = data['pre-coalescence-grammar.json']
    final = data['grammar.json']
    projection = data['bank-projection.json']
    sharing = data['bank-coalescence.json']
    invariant = data['coalescence-invariant.json']
    graph, context_summary = endpoint.closure(original, context)
    assert context['output_grammar_sha256'] == jd(pre)
    zero_rows = set(map(tuple, context['zero_rows']))
    assert len(zero_rows) == len(context['zero_rows'])
    invocations = defaultdict(list)
    for i, (_, op, node, bit) in enumerate(graph.leaves):
        if context['states_at_occurrences'][i] is not None:
            invocations[node, bit].append(i)
    for pair in zero_rows:
        assert invocations[pair], 'claimed zero has no admitted occurrence'
        op = original['nodes'][pair[0]][pair[1]]['op']
        kind, operand = endpoint.operand(op)
        assert kind in ('decnz', 'half')
        slot = original['registers'].index(operand)
        assert all(context['states_at_occurrences'][i][slot] == '1' for i in invocations[pair])
    a = core(graph, zero_rows)
    b = core(endpoint.Graph(pre))
    c = core(endpoint.Graph(contracted))
    assert a == b == c
    control = data['control-certificate.json']
    assert control['source_sha256'] == SOURCE_SHA
    assert control['contextual_output_grammar_sha256'] == jd(pre)
    assert control['finite_control_output_grammar_sha256'] == jd(contracted)
    assert control['projected_grammar_sha256'] == jd(projected)
    assert control['final_grammar_sha256'] == jd(final)

    assert projection['before_grammar_sha256'] == jd(contracted)
    assert projection['after_grammar_sha256'] == jd(projected)
    assert {k:v for k,v in contracted.items() if k != 'registers'} == {
        k:v for k,v in projected.items() if k != 'registers'}
    used, halves = set(), set()
    for pair in contracted['nodes']:
        for child in pair:
            op = child.get('op', '')
            if op.startswith('3.'):
                kind, name = endpoint.operand(op)
                used.add(name)
                if kind == 'half': halves.add(name)
    old = contracted['registers']
    kept = [n for n in old if n in halves] + [n for n in old if n in used and n not in halves]
    omitted = [n for n in old if n not in used]
    assert kept == projected['registers'] == projection['retained_register_order']
    assert omitted == projection['removed_registers']
    assert projection['removed_interpretation'] == dict.fromkeys(omitted, 0)
    assert projection['old_to_new'] == [kept.index(n) if n in kept else None for n in old]
    shared_graph, shared_summary = endpoint.closure(projected, invariant)
    assert sharing['before_grammar_sha256'] == jd(projected)
    assert sharing['after_grammar_sha256'] == jd(final)
    assert sharing['invariant_sha256'] == jd(invariant)
    groups = sharing['groups']
    flattened = [n for group in groups.values() for n in group]
    assert all(groups.values()) and len(flattened) == len(set(flattened)) == len(kept)
    assert set(flattened) == set(kept) and set(groups) == set(final['registers'])
    mapping = {n:key for key, group in groups.items() for n in group}
    assert mapping == sharing['mapping']
    checked, shared_sites = 0, 0
    for i, (op, *_) in enumerate(shared_graph.rows):
        state = invariant['states_at_occurrences'][i]
        if state is None or not op.startswith('3.'): continue
        _, name = endpoint.operand(op)
        peers = [n for n in groups[mapping[name]] if n != name]
        assert all(state[kept.index(n)] == '1' for n in peers)
        checked += 1
        shared_sites += bool(peers)
    assert checked == sharing['all_reached_operations_checked']
    assert core(shared_graph, rename=mapping) == core(endpoint.Graph(final))
    return dict(context=context_summary, proven_zero_rows=len(zero_rows),
                retained_operation_graph_rows=len(a['rows']), independent_core_sha256=jd(a),
                source_carrier=len(old), projected=len(kept), physical_classes=len(groups),
                omitted_zero_coordinates=omitted, sharing=shared_summary,
                checked_operations=checked, zero_peer_sites=shared_sites)


def fresh_domain(parent, selected, pdata, sdata):
    names = pdata['names.json']
    raw_header, raw = endpoint.table(parent/'raw.tm')
    assert set(names.values()) == set(range(int(raw_header['states'])))
    assert len(names) == len(set(names.values()))
    requested = {(name, int(bit)) for name, bit in pdata['selector.json']['new_totalized_rows']}
    assert requested == set(SEMANTIC_EXCLUSIONS.items())
    assert all(name in names for name, _ in requested)
    blocked = {(names[name], bit) for name, bit in requested}
    sink = names['silent.sink']
    blocked |= {(sink, 0), (sink, 1)}
    # The raw sink has no incoming rows outside the independently justified set.
    assert {(q, bit) for (q, bit), (_, _, target, _) in raw.items() if target == sink} == blocked
    parent_map = pdata['quotient.json']
    parent_header, companion = endpoint.table(parent/'machine.tm')
    preimages = defaultdict(list)
    for q in range(int(raw_header['states'])):
        preimages[endpoint.mapped(parent_map, q)].append(q)
    holes = {(q, bit) for q, olds in preimages.items() for bit in (0,1)
             if all((old, bit) in blocked for old in olds)}
    domain = sdata['domain.json']
    assert domain['source_sha256'] == SOURCE_SHA
    assert domain['control_sha256'] == sha(parent/'machine.tm')
    assert domain['names_sha256'] == sha(parent/'names.json')
    assert domain['raw_quotient_sha256'] == sha(parent/'quotient.json')
    assert domain['source_request_file_sha256'] == sha(parent/'selector.json')
    assert {tuple(x) for x in domain['holes']} == holes
    assert domain['preimages'] == {str(q):preimages[q] for q, _ in sorted(holes)}
    assert domain['sink'] == endpoint.mapped(parent_map, sink)
    assert all(companion[key][2] == domain['sink'] for key in holes)
    completed_header, completed = endpoint.table(selected/'raw.tm')
    assert completed_header == parent_header
    assert all(completed[key] == companion[key] for key in companion if key not in holes)
    completion = sdata['completion.json']
    assert completion['source_sha256'] == sha(parent/'machine.tm')
    assert completion['target_sha256'] == sha(selected/'raw.tm')
    assert completion['retained_rows'] == len(companion)-len(holes)
    assert completion['changes'] == [dict(state=q, read=bit, before=list(companion[q,bit]),
                                         after=list(completed[q,bit])) for q,bit in sorted(holes)]
    # All-row B and ingress quotients include every row filled above.
    _, _, parent_counts = endpoint.row_maps(parent)
    bmap, emap, selected_counts = endpoint.row_maps(selected)
    assert (parent_counts['raw'], parent_counts['B_exit'], parent_counts['marked']) == (395,392,391)
    assert (selected_counts['raw'], selected_counts['B_exit'], selected_counts['marked']) == (392,388,387)
    assert endpoint.mapped(bmap,0) == endpoint.mapped(bmap,1) - 1 == 0
    assert [q for q in range(int(parent_header['states'])) if endpoint.mapped(bmap,q) == 1] == [1]
    plan = json.loads((PHASE/'plans/normalized_prefix/completion.json').read_text())
    assert plan['control_sha256'] == sha(parent/'machine.tm')
    assert plan['source_sha256'] == SOURCE_SHA and plan['convention'] == 'B'
    assert plan['mapping'] == [endpoint.mapped(bmap,q) for q in range(int(parent_header['states']))]
    assert plan['holes'] == [list(key) for key in sorted(holes)]
    for folder, data in ((parent,pdata), (selected,sdata)):
        event_certificate = data['event-quotient.json']
        assert event_certificate['source_B'] == 1 and event_certificate['time_shift'] == -1
        assert event_certificate['source_table_sha256'] == sha(folder/'machine.tm')
        assert event_certificate['predecessor_sha256'] == sha(folder/'ingress-prequotient.tm')
        assert event_certificate['result_sha256'] == sha(folder/'events.tm')
        _, b_rows = endpoint.table(folder/'machine.tm')
        assert all(b_rows[1,z][2] != 1 for z in (0,1))
    return dict(raw_excluded_requests=len(requested), projected_holes=len(holes),
                retained_rows=len(companion)-len(holes),
                actually_changed_rows=sum(companion[key] != completed[key] for key in holes),
                parent_counts=parent_counts, selected_counts=selected_counts,
                holes=[list(key) for key in sorted(holes)])


def rejected(action):
    try:
        action()
    except (AssertionError, KeyError, IndexError, ValueError):
        return True
    raise AssertionError('damaged input was not rejected')


def adversarial(parent, selected, pdata, sdata):
    checks = []
    bad = deepcopy(pdata)
    graph = endpoint.Graph(bad['contextual-tree-certificate.json']['input_grammar'])
    state = list(bad['contextual-tree-certificate.json']['states_at_occurrences'][graph.entry])
    state[0] = '2'
    bad['contextual-tree-certificate.json']['states_at_occurrences'][graph.entry] = ''.join(state)
    rejected(lambda:storage(bad)); checks.append('false contextual zero entry')
    bad = deepcopy(pdata)
    for pair in bad['pre-projection-grammar.json']['nodes']:
        for child in pair:
            if child.get('op','').startswith('3.$native-half:'):
                child['op'] = '3.' + child['op'].split(':',1)[1]
                break
        else: continue
        break
    bad['control-certificate.json']['finite_control_output_grammar_sha256'] = jd(bad['pre-projection-grammar.json'])
    bad['bank-projection.json']['before_grammar_sha256'] = jd(bad['pre-projection-grammar.json'])
    rejected(lambda:storage(bad)); checks.append('native half reinterpreted as decrement, digests updated')
    bad = deepcopy(pdata)
    bad['bank-projection.json']['removed_interpretation'][bad['bank-projection.json']['removed_registers'][0]] = 1
    rejected(lambda:storage(bad)); checks.append('nonzero omitted coordinate')
    bad = deepcopy(pdata)
    inv = bad['coalescence-invariant.json']
    graph = endpoint.Graph(inv['input_grammar'])
    state = list(inv['states_at_occurrences'][graph.entry]); state[-1] = '2'
    inv['states_at_occurrences'][graph.entry] = ''.join(state)
    bad['bank-coalescence.json']['invariant_sha256'] = jd(inv)
    rejected(lambda:storage(bad)); checks.append('false sharing zero entry, digest updated')
    bad = deepcopy(sdata); bad['domain.json']['holes'].append([0,0])
    rejected(lambda:fresh_domain(parent,selected,pdata,bad)); checks.append('invented completion hole')
    bad = deepcopy(sdata); bad['domain.json']['preimages'][str(bad['domain.json']['holes'][0][0])] = []
    rejected(lambda:fresh_domain(parent,selected,pdata,bad)); checks.append('omitted raw quotient preimages')
    bad = deepcopy(pdata); bad['selector.json']['new_totalized_rows'].append(['bootstrap', '0'])
    rejected(lambda:fresh_domain(parent,selected,bad,sdata)); checks.append('unsupported named exclusion')
    bad = deepcopy(pdata); bad['allocation.json']['functions']['accept']['colours']['state'] = bad['allocation.json']['functions']['accept']['colours']['right']
    rejected(lambda:source_cfg(SOURCE,bad['allocation.json'])); checks.append('simultaneously live source alias')
    before = endpoint.table(selected/'raw.tm')[1]
    after = endpoint.table(selected/'machine.tm')[1]
    marked = endpoint.table(selected/'events.tm')[1]
    ingress = endpoint.table(selected/'ingress-prequotient.tm')[1]
    mapping = sdata['quotient.json']
    event_mapping = sdata['event-quotient.json']['mapping']

    def equations(a,b,m):
        assert {endpoint.mapped(m,q) for q in range(len(a)//2)} == set(range(len(b)//2))
        assert endpoint.mapped(m,0) == 0
        for (q,z),(w,d,t,e) in a.items():
            assert b[endpoint.mapped(m,q),z] == (w,d,endpoint.mapped(m,t),e)

    equations(before,after,mapping)
    equations(ingress,marked,event_mapping)
    for field,label in [(0,'write'),(1,'move'),(2,'target'),(3,'B color')]:
        damaged = dict(after); row = list(damaged[0,0])
        row[field] = [1-row[0], 'L' if row[1] == 'R' else 'R',
                      (row[2]+1) % (len(after)//2), 1-row[3]][field]
        damaged[0,0] = tuple(row)
        rejected(lambda:equations(before,damaged,mapping)); checks.append('damaged retained '+label)
    damaged = deepcopy(mapping); damaged['1'] = 0
    rejected(lambda:equations(before,after,damaged)); checks.append('B merged with start')
    damaged = dict(marked); key = next(k for k,v in damaged.items() if v[3])
    row = damaged[key]; damaged[key] = (*row[:3],0)
    rejected(lambda:equations(ingress,damaged,event_mapping)); checks.append('marked event erased')
    bad = deepcopy(sdata); bad['event-quotient.json']['time_shift'] = 0
    rejected(lambda:fresh_domain(parent,selected,pdata,bad)); checks.append('event time shift erased')
    return checks


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--parent', required=True, type=Path)
    parser.add_argument('--selected', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    assert sha(SOURCE) == SOURCE_SHA
    pdata, sdata = load(args.parent), load(args.selected)
    for data, folder in ((pdata,args.parent),(sdata,args.selected)):
        metadata = data['metadata.json']
        assert metadata['source_sha256'] == SOURCE_SHA
        for key,name in [('raw_table_sha256','raw.tm'),('table_sha256','machine.tm'),('event_table_sha256','events.tm')]:
            assert metadata[key] == sha(folder/name)
    result = dict(format='np-conp-normalized-selected-independent-implementation-v1',
                  reviewer='internal-model-reviewer', source_sha256=SOURCE_SHA,
                  checker_sha256=sha(Path(__file__)), reused_checker_sha256=ENDPOINT_SHA,
                  runtime=runtime_inheritance(args.parent,pdata),
                  source_allocation=source_cfg(SOURCE,pdata['allocation.json']),
                  storage=storage(pdata), domain_and_rows=fresh_domain(args.parent,args.selected,pdata,sdata),
                  adversarial_rejections=adversarial(args.parent,args.selected,pdata,sdata),
                  artifacts={label:{p.name:sha(p) for p in sorted(folder.iterdir()) if p.is_file()}
                             for label,folder in [('parent',args.parent),('selected',args.selected)]},
                  scope='Nonauthor internal model-agent implementation review of these exact bytes. Conventional proof, finite executable certificate checks, literal tests, Lean and CI are separate. Literal evidence is in a separate receipt.')
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'artifacts'},sort_keys=True,indent=2))


if __name__ == '__main__':
    main()
