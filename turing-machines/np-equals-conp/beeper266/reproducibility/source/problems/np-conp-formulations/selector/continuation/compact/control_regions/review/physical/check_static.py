"""Nonauthor occurrence-control, storage, runtime and complete-row checks.

This review does not import the producer's compiler, analyzer, contextual
specializer, rotation search or completion solver.  The existing independently
authored tuple interpreter, source-CFG and literal row checkers are pinned.
"""
from collections import Counter, defaultdict, deque
from copy import deepcopy
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess

HERE = Path(__file__).resolve().parent
COMPACT = HERE.parents[2]
PRIOR = COMPACT / 'operand_dispatch/review/physical/check_static.py'
PIN = 'f3e6f5f7b8ab2caa70640db6c21241cb5e9d32b774123c35a7b615e5245ad7ab'
CONTROL = COMPACT / 'operand_dispatch/machines/control_mode_parent'
CONTROL_PRODUCER = 'cc55f5e39a98b75062fdd8ad2029ae9a0efeef13'
EXCLUDED = {'1b.reg.prep_1': 1, '2h.native_half.begin': 0,
            '2h.native_half.boundary': 1, '2h.native_half.prep': 1,
            '2h.native_half.undo': 0}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


assert sha(PRIOR) == PIN
spec = importlib.util.spec_from_file_location('independent_occurrence_predecessor', PRIOR)
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)
base = prior.base
storage_base = base.storage_checker
endpoint = base.endpoint
phase = prior.prior
dispatcher = prior.previous


def occurrence_core(graph, omitted=frozenset()):
    """Erase named *occurrences*, without changing other shared-node uses."""
    omitted = set(omitted)
    def forward(position):
        seen = set()
        while position in omitted or graph.rows[position][0].startswith(('_break.', '_continue.')):
            assert position not in seen, 'administrative-only cycle'
            seen.add(position)
            op, *targets = graph.rows[position]
            if position in omitted:
                assert endpoint.operand(op)[0] in ('decnz', 'half')
                position = targets[1]
            else:
                position = targets[0]
        return position
    for position in range(len(graph.rows)):
        forward(position)
    entry = forward(graph.entry)
    ids, queue, rows = {entry: 0}, deque([entry]), []
    while queue:
        position = queue.popleft()
        op, *targets = graph.rows[position]
        targets = [forward(target) for target in targets]
        for target in targets:
            if target not in ids:
                ids[target] = len(ids)
                queue.append(target)
        rows.append([op, *[ids[target] for target in targets]])
    return dict(entry=0, rows=rows)


def contextual_step(certificate, output):
    """Postfixed closure plus exact all-branch core equality for old cleanup."""
    before = certificate['input_grammar']
    graph, closure = endpoint.closure(before, certificate)
    assert certificate['output_grammar_sha256'] == digest(output)
    zero_rows = set(map(tuple, certificate['zero_rows']))
    assert len(zero_rows) == len(certificate['zero_rows'])
    invocations = defaultdict(list)
    for index, (_, _, node, bit) in enumerate(graph.leaves):
        if certificate['states_at_occurrences'][index] is not None:
            invocations[node, bit].append(index)
    for pair in zero_rows:
        assert invocations[pair]
        op = before['nodes'][pair[0]][pair[1]]['op']
        kind, name = endpoint.operand(op)
        assert kind in ('decnz', 'half')
        slot = before['registers'].index(name)
        assert all(certificate['states_at_occurrences'][index][slot] == '1'
                   for index in invocations[pair])
    left = storage_base.core(graph, zero_rows)
    right = storage_base.core(endpoint.Graph(output))
    assert left == right, 'contextual retained graph differs'
    return dict(closure=closure, shared_zero_rows=len(zero_rows),
                retained_core_sha256=digest(left), output_grammar_sha256=digest(output))


def zero_chain(data):
    certificate = data['zero-context.json']
    assert certificate['format'] == 'np-conp-occurrence-zero-specialization-v1'
    before = certificate['input_grammar']
    middle = certificate['specialized_grammar']
    assert digest(before) == certificate['input_grammar_sha256']
    assert digest(middle) == certificate['specialized_grammar_sha256']
    assert 'neutral-context.json' not in data, 'neutral producer is outside this selected review'
    output = data['pre-control-grammar.json']
    assert digest(output) == certificate['output_grammar_sha256']
    first = contextual_step(data['contextual-tree-certificate.json'], before)
    invariant = dict(input_grammar=before, input_grammar_sha256=digest(before),
                     states_at_occurrences=certificate['input_abstract_states'])
    graph, closure = endpoint.closure(before, invariant)
    expected, selected = {}, set()
    for index, (path, op, _, _) in enumerate(graph.leaves):
        state = certificate['input_abstract_states'][index]
        if state is None or not op.endswith('.decnz'):
            continue
        kind, name = endpoint.operand(op)
        assert kind in ('decnz', 'half')
        if state[before['registers'].index(name)] == '1':
            selected.add(index)
            expected[''.join(map(str, path))] = dict(index=index, operation=op,
                register=name, state=state)
    assert certificate['replacements'] == expected, 'occurrence/operand inventory differs'
    emitted, interned = [], {}
    def visit(child, path):
        if 'op' in child:
            return {'op': '_break.1' if path in expected else child['op']}
        pair = [visit(value, path + str(bit))
                for bit, value in enumerate(before['nodes'][child['node']])]
        key = json.dumps(pair, sort_keys=True, separators=(',', ':'))
        if key not in interned:
            interned[key] = len(emitted)
            emitted.append(pair)
        return {'node': interned[key]}
    root = visit({'node': before['root']}, '110')['node']
    assert middle == dict(registers=before['registers'], nodes=emitted, root=root), \
        'specialization changes an unselected leaf or its path'
    a = occurrence_core(graph, selected)
    b = storage_base.core(endpoint.Graph(middle))
    assert a == b, 'false lexical return does not match removed zero occurrence'
    assert certificate['cleanup_certificate']['input_grammar'] == middle, 'cleanup input is disconnected from specialization'
    assert certificate['cleanup_certificate']['input_grammar_sha256'] == digest(middle)
    cleanup = contextual_step(certificate['cleanup_certificate'], output)
    return dict(first_context=first, postfixed_closure=closure,
                replaced_occurrences=len(selected), replacements=expected,
                specialized_core_sha256=digest(a), cleanup=cleanup,
                scope='all finite source-entry runs by inductive closure; no blank bootstrap inferred')


def storage(data):
    chain = zero_chain(data)
    pre = data['pre-control-grammar.json']
    contracted = data['pre-projection-grammar.json']
    projected = data['pre-coalescence-grammar.json']
    final = data['grammar.json']
    projection = data['bank-projection.json']
    sharing = data['bank-coalescence.json']
    invariant = data['coalescence-invariant.json']
    a = storage_base.core(endpoint.Graph(pre))
    assert a == storage_base.core(endpoint.Graph(contracted)), 'rotation changed a retained edge'
    control = data['control-certificate.json']
    assert control['source_sha256'] == storage_base.SOURCE_SHA
    for field, grammar in [('contextual_output_grammar_sha256', pre),
                           ('finite_control_output_grammar_sha256', contracted),
                           ('projected_grammar_sha256', projected),
                           ('final_grammar_sha256', final)]:
        assert control[field] == digest(grammar), field
    assert projection['before_grammar_sha256'] == digest(contracted)
    assert projection['after_grammar_sha256'] == digest(projected)
    assert {k: v for k, v in contracted.items() if k != 'registers'} == \
           {k: v for k, v in projected.items() if k != 'registers'}
    used, halves = set(), set()
    for pair in contracted['nodes']:
        for child in pair:
            op = child.get('op', '')
            if op.startswith('3.'):
                kind, name = endpoint.operand(op)
                used.add(name)
                if kind == 'half':
                    halves.add(name)
    old = contracted['registers']
    kept = [name for name in old if name in halves] + [name for name in old if name in used and name not in halves]
    omitted = [name for name in old if name not in used]
    assert kept == projected['registers'] == projection['retained_register_order']
    assert omitted == projection['removed_registers']
    assert projection['removed_interpretation'] == dict.fromkeys(omitted, 0)
    assert projection['old_to_new'] == [kept.index(name) if name in kept else None for name in old]
    graph, closure = endpoint.closure(projected, invariant)
    assert sharing['before_grammar_sha256'] == digest(projected)
    assert sharing['after_grammar_sha256'] == digest(final)
    assert sharing['invariant_sha256'] == digest(invariant)
    groups = sharing['groups']
    flattened = [name for group in groups.values() for name in group]
    assert all(groups.values()) and len(flattened) == len(set(flattened)) == len(kept)
    assert set(flattened) == set(kept) and set(groups) == set(final['registers'])
    mapping = {name: key for key, group in groups.items() for name in group}
    assert mapping == sharing['mapping']
    checked = peer_sites = peer_obligations = 0
    for index, (op, *_) in enumerate(graph.rows):
        state = invariant['states_at_occurrences'][index]
        if state is None or not op.startswith('3.'):
            continue
        _, name = endpoint.operand(op)
        peers = [peer for peer in groups[mapping[name]] if peer != name]
        assert all(state[kept.index(peer)] == '1' for peer in peers), (index, name)
        checked += 1
        peer_sites += bool(peers)
        peer_obligations += len(peers)
    assert checked == sharing['all_reached_operations_checked']
    assert storage_base.core(graph, rename=mapping) == storage_base.core(endpoint.Graph(final))
    return dict(occurrence_chain=chain, retained_core_rows=len(a['rows']),
                independent_core_sha256=digest(a), allocated=len(old), projected=len(kept),
                physical_classes=len(groups), projected_away_zero_coordinates=omitted,
                sharing_closure=closure, checked_operations=checked,
                zero_peer_sites=peer_sites, zero_peer_obligations=peer_obligations,
                core_preserving_moves=len(control['moves']))


def grammar_rows(rows, grammar):
    names = {index: 'main().0' if index == grammar['root'] else f'compact_grammar_{index}.0'
             for index in range(len(grammar['nodes']))}
    assert {name for name, _ in rows if name.startswith('compact_grammar_') or name == 'main().0'} == set(names.values())
    count = 0
    for index, pair in enumerate(grammar['nodes']):
        for bit, child in enumerate(pair):
            if 'node' in child:
                expected = (bit, 'R', names[child['node']], 0)
            else:
                op = child['op']
                if op.startswith('_break.'):
                    level = int(op.split('.')[1])
                    if bit == 0 and level == 0:
                        expected = (1, 'L', '6.continue.0', 0)
                    else:
                        expected = (0, 'L', '6.break.' + str(level - int(bit == 0)), 0)
                elif op.startswith('_continue.'):
                    level = int(op.split('.')[1]) - bit
                    assert level >= 0
                    expected = (0, 'L', '6.continue.' + str(level), 0)
                else:
                    assert op == 'beep' or op.startswith('3.')
                    expected = (bit, 'R', op, 0)
            assert rows[names[index], bit] == expected, (names[index], bit)
            count += 1
    return count


def runtime(parent, data):
    # Public export: immutable content pins replace unavailable private Git history.
    control_pins = {'raw.tm': 'd35f7ebeef3b0198fc90de9d172da5202d74cf607dc315fe941fba5993ec8173', 'names.json': 'd296e840c9ba995c7bda7181e4f6eea48fa99f82eff49f5f4568e19102ece1dd'}
    for filename, expected in control_pins.items():
        assert sha(CONTROL / filename) == expected
    names = data['names.json']
    rows = dispatcher.named_rows(parent, names)
    old = dispatcher.named_rows(CONTROL, read(CONTROL / 'names.json'))
    grammar = data['grammar.json']
    order = grammar['registers']
    assert 1 <= len(order) <= 1909
    prior.selector_rows(rows, order)
    selector = data['selector.json']
    assert selector['kind'] == 'np-conp-control-mode-selector-v1'
    assert set(map(tuple, selector['new_totalized_rows'])) == {(name, str(bit)) for name, bit in EXCLUDED.items()}
    assert selector['operation_entries'] == [dict(register=register, index=index,
        operation=mode, terminal=f'3.{register}.{suffix}') for index, register in enumerate(order)
        for mode, suffix in (('inc', 'inc'), ('dec', 'decnz'))]
    native = data['native-runtime.json']['operands']
    assert order[:len(native)] == native
    expected_operations = {f'3.{register}.{kind}' for register in order for kind in ('inc', 'decnz')}
    expected_operations |= {'3.$native-half:' + register + '.decnz' for register in native}
    assert {name for name in names if name.startswith('3.')} == expected_operations
    for index, register in enumerate(native):
        name = '3.$native-half:' + register + '.decnz'
        assert rows[name, 0] == (1, 'R', '2h.native_half.prep', 0)
        assert rows[name, 1] == (0, 'R', '2h.native_half.select.' + str(index), 0)
    geometry = dispatcher.geometry(grammar, data['dispatcher.json'])
    limit = data['dispatcher.json']['limit']
    dispatcher.delimiter_rows(rows, limit)
    assert {name for name in names if name.startswith('repeat.dispatch.')} == \
           {'repeat.dispatch.' + str(index) for index in range(limit)}
    count = grammar_rows(rows, grammar)
    inherited = new_lexical = 0
    for (name, bit), row in rows.items():
        if name.startswith('compact_grammar_') or name == 'main().0':
            continue
        if name.startswith('3.') or (name, bit) in {
                ('0a.boot1.C', 1), ('0b.boot2.2', 0), ('0b.boot2.2', 1)}:
            # These rows depend on the freshly checked physical permutation.
            # selector_rows and the explicit native entry loop checked them.
            continue
        if name.startswith('repeat.dispatch.') or (name, bit) == ('6.continue.0', 1):
            continue
        if name.startswith('6.break.') and name not in {key[0] for key in old}:
            level = int(name.rsplit('.', 1)[1]); assert level > 1
            assert row == (0, 'L', '6.break.' + str(level - 1 if bit == 0 else level), 0)
            new_lexical += 1
        elif name.startswith('6.continue.') and name not in {key[0] for key in old}:
            level = int(name.rsplit('.', 1)[1]); assert level > 0
            assert row == (0, 'L', '6.continue.' + str(level if bit == 0 else level - 1), 0)
            new_lexical += 1
        else:
            assert row == old[name, bit], (name, bit)
            inherited += 1
    assert data['metadata.json']['bootstrap_zero_register_capacity'] == 1909
    maximum = max(len(path) for path, *_ in endpoint.Graph(grammar).leaves)
    assert maximum == data['metadata.json']['max_leaf_path']
    assert data['metadata.json']['bootstrap_bank_anchor_after_translation'] == 3824
    assert maximum < 3822, 'prepared terminal reaches the counted bank anchor'
    coverage = dict(grammar=count, operation_entries=2 * len(expected_operations),
                    bootstrap_calls=3, delimiter=2 * limit + 1,
                    inherited_runtime=inherited, added_lexical_return_rows=new_lexical)
    assert sum(coverage.values()) == len(rows), 'incomplete or overlapping named row coverage'
    return dict(frozen_runtime_producer=CONTROL_PRODUCER,
                exact_inherited_named_runtime_rows=inherited,
                independently_checked_grammar_rows=count,
                complete_disjoint_raw_row_coverage=coverage,
                operation_entries=2 * len(order), native_entries=len(native),
                physical_classes=len(order), paid_bootstrap_fields=1909,
                delimiter_geometry=geometry,
                excluded_named_reads=[[name, bit] for name, bit in sorted(EXCLUDED.items())],
                startup_scope='must be established on this exact new raw table by independent literal execution')


def extra_mutations(data, parent):
    rejected = []
    def reject(label, call):
        try:
            call()
        except (AssertionError, KeyError, IndexError, ValueError, TypeError):
            rejected.append(label)
        else:
            raise AssertionError('mutation escaped: ' + label)
    bad = deepcopy(data)
    bad['zero-context.json']['input_grammar_sha256'] = '0' * 64
    reject('occurrence input binding', lambda: zero_chain(bad))
    path = next(iter(data['zero-context.json']['replacements']))
    bad = deepcopy(data); bad['zero-context.json']['replacements'].pop(path)
    reject('omitted occurrence', lambda: zero_chain(bad))
    bad = deepcopy(data); bad['zero-context.json']['replacements'][path]['register'] = 'wrong'
    reject('wrong occurrence operand', lambda: zero_chain(bad))
    bad = deepcopy(data)
    selected = bad['zero-context.json']['replacements'].pop(path)
    bad['zero-context.json']['replacements'][path + '0'] = selected
    reject('wrong occurrence path', lambda: zero_chain(bad))
    bad = deepcopy(data)
    certificate = bad['zero-context.json']; replacement = certificate['replacements'][path]
    index = replacement['index']; slot = certificate['input_grammar']['registers'].index(replacement['register'])
    state = certificate['input_abstract_states'][index]
    certificate['input_abstract_states'][index] = state[:slot] + '2' + state[slot + 1:]
    reject('false occurrence zero mask', lambda: zero_chain(bad))
    bad = deepcopy(data)
    certificate = bad['zero-context.json']
    changed = False
    for pair in certificate['specialized_grammar']['nodes']:
        for child in pair:
            if child == {'op': '_break.1'} and not changed:
                child['op'] = '_break.0'; changed = True
    assert changed
    certificate['specialized_grammar_sha256'] = digest(certificate['specialized_grammar'])
    reject('changed false return with updated digest', lambda: zero_chain(bad))
    bad = deepcopy(data)
    bad['zero-context.json']['cleanup_certificate']['output_grammar_sha256'] = '0' * 64
    reject('cleanup output binding', lambda: zero_chain(bad))
    bad = deepcopy(data)
    output = bad['pre-control-grammar.json']
    clean = bad['zero-context.json']['cleanup_certificate']
    clean.update(input_grammar=deepcopy(output), input_grammar_sha256=digest(output),
        output_grammar_sha256=digest(output), zero_rows=[],
        states_at_occurrences=['7' * len(output['registers'])] * len(endpoint.Graph(output).rows))
    # The detached identity certificate is independently internally valid.
    # Only its missing connection to the specialized grammar makes it invalid.
    contextual_step(clean, output)
    reject('disconnected cleanup with valid identity closure', lambda: zero_chain(bad))
    rows = dispatcher.named_rows(parent, data['names.json'])
    badrows = dict(rows)
    key = next(key for key in rows if key[0].startswith('compact_grammar_'))
    w, d, t, e = badrows[key]; badrows[key] = (1 - w, d, t, e)
    reject('compiled grammar write', lambda: grammar_rows(badrows, data['grammar.json']))
    badrows = dict(rows)
    key = ('repeat.dispatch.0', 1)
    badrows[key] = (1, 'L', 'repeat.dispatch.1', 0)
    reject('delimiter fails to reset', lambda: dispatcher.delimiter_rows(badrows, data['dispatcher.json']['limit']))
    return rejected


def ledger(parent, selected, data):
    """Compose all three maps and count each complete event-state fiber once."""
    names = data['names.json']
    first = base.completion.map_list(read(parent / 'quotient.json'), len(names))
    second_data = read(selected / 'quotient.json')
    second = base.completion.map_list(second_data,
        len(base.completion.parse(selected / 'raw.tm')[1]) // 2)
    third = base.completion.map_list(read(selected / 'event-quotient.json')['mapping'],
        len(base.completion.parse(selected / 'ingress-prequotient.tm')[1]) // 2)
    def category(name):
        if name.startswith('compact_grammar_') or name == 'main().0':
            return 'compiled arithmetic and control'
        if name.startswith('3.$native-half:'):
            return 'native half operation entries'
        if name.startswith('3.'):
            return 'register operation entries'
        if name.startswith('repeat.dispatch.'):
            return 'return delimiter scan'
        parts = name.split('.')
        if len(parts) == 4 and parts[:2] == ['2b', 'reg'] and parts[2].isdigit() and parts[3] in ('inc', 'dec'):
            return 'operation-specific operand selectors'
        if name.startswith('2h.native_half.select.') or name == '2h.native_half.prep':
            return 'native half selection and preparation'
        if name.startswith('2h.native_half.'):
            return 'native half kernel'
        if name.startswith('0a.boot1.'):
            return 'blank bootstrap'
        if name in ('beep', 'B'):
            return 'event adapter'
        if name == 'silent.sink':
            return 'totalization'
        return 'remaining engine and dispatch'
    classes = defaultdict(set)
    for name, raw in names.items():
        classes[third[second[first[raw]]]].add(category(name))
    supplied = read(selected / 'physical-ledger.json')
    expected = {str(key): sorted(value) for key, value in classes.items()}
    assert supplied['classes'] == expected
    states = len(base.completion.parse(selected / 'events.tm')[1]) // 2
    assert set(classes) == set(range(states))
    assert supplied['states'] == states and supplied['rows'] == 2 * states
    assert supplied['event_table_sha256'] == sha(selected / 'events.tm')
    assert supplied['source_sha256'] == data['metadata.json']['source_sha256']
    partition = Counter(' + '.join(sorted(value)) for value in classes.values())
    assert dict(partition) == supplied['disjoint_event_partition']
    return dict(states=states, rows=2 * states, disjoint_partition=dict(sorted(partition.items())),
                all_raw_origins=len(names), complete_state_fibers=len(classes),
                source_table_sha256=sha(selected / 'events.tm'))


def run(parent, selected, plan, source):
    parent, selected, plan, source = map(Path, (parent, selected, plan, source))
    old_storage, old_runtime = storage_base.storage, base.runtime
    old_source_allocation, old_excluded = base.source_allocation, base.completion.EXCLUDED
    def allocation(path, data):
        result = old_source_allocation(path, data)
        result['three_transfer_swap'] = phase.swaps(path, data)
        return result
    storage_base.storage, base.runtime = storage, runtime
    base.source_allocation, base.completion.EXCLUDED = allocation, EXCLUDED
    try:
        result = base.run(parent, selected, plan, source)
    finally:
        storage_base.storage, base.runtime = old_storage, old_runtime
        base.source_allocation, base.completion.EXCLUDED = old_source_allocation, old_excluded
    data = {path.name: read(path) for path in parent.glob('*.json')}
    result['format'] = 'np-conp-occurrence-control-independent-physical-static-v1'
    result['reviewer'] = 'internal-model-reviewer; nonauthor of selected control_regions producer'
    result['authorship'] = ('author of separate losing record_tail experiments; conceptually suggested inspecting '
        'known-zero clears, but authored none of the selected source, specializer, grammar plan, compiler, completion or tables')
    result['checker_sha256'] = sha(__file__)
    result['pinned_predecessor_checker_sha256'] = PIN
    result['damaged_certificates_rejected'] += extra_mutations(data, parent)
    bad = deepcopy(data); bad['three-move-swap.json'][0]['work'] = 'main.left'
    try:
        phase.swaps(source, bad)
    except AssertionError:
        result['damaged_certificates_rejected'].append('aliased or wrong swap work certificate')
    else:
        raise AssertionError('aliased swap work certificate accepted')
    result['physical_ledger'] = ledger(parent, selected, data)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('parent', 'selected', 'plan', 'source', 'out'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    result = run(args.parent, args.selected, args.plan, args.source)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('storage', 'runtime', 'completion',
                                                   'damaged_certificates_rejected')}, sort_keys=True, indent=2))
