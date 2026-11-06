"""Generate a kernel-checked expansion trace for the literal 284 grammar AST.

The Python-generated checkpoints are untrusted: each transition chunk is
proved by Lean `rfl`, and the final theorem composes them. The input JSON and
generated Lean AST are not thereby proved equal. Run from the repository root:

  python3 Shared/Beeping/NPcoNP/generate_grammar284_trace.py OUTPUT_DIRECTORY
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

INPUT = Path('Shared/Beeping/NPcoNP/Inputs/parent290-grammar.json')
PREFIX = 'Shared.Beeping.NPcoNP.ExpansionTrace'
NAMESPACE = 'Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace'


def boolean_list(xs):
    return '[' + ', '.join('true' if x else 'false' for x in xs) + ']'


def natural_list(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def leaf(value):
    if 'node' in value:
        assert set(value) == {'node'}
        return '.node ' + str(value['node'])
    assert set(value) == {'op'}
    return '.op ' + json.dumps(value['op'], ensure_ascii=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output_directory', type=Path)
    args = parser.parse_args()
    grammar = json.loads(INPUT.read_text())
    nodes = grammar['nodes']
    assert grammar['root'] == 159 and len(nodes) == 160
    pending = [(53, {'node': grammar['root']}, (True, True, False), ())]
    starts, leaves, snapshots = [], [], {}

    def snapshot(step):
        snapshots[step] = (pending.copy(), starts.copy(), leaves.copy())

    snapshot(0)
    step = 0
    while pending:
        fuel, item, path, ancestors = pending.pop(0)
        assert fuel > 0
        starts.append((path, len(leaves)))
        if 'op' in item:
            leaves.append((path, item['op']))
        else:
            index = item['node']
            assert index not in ancestors
            left, right = nodes[index]
            pending[0:0] = [(fuel - 1, left, path + (False,), (index,) + ancestors),
                            (fuel - 1, right, path + (True,), (index,) + ancestors)]
        step += 1
        if step % 10 == 0 or not pending:
            snapshot(step)
    assert step == 557 and len(starts) == 557 and len(leaves) == 279

    paths, ancestor_lists = {}, {}

    def path_name(path):
        if path not in paths:
            paths[path] = len(paths)
        return 'p' + str(paths[path])

    def ancestors_name(ancestors):
        if ancestors not in ancestor_lists:
            ancestor_lists[ancestors] = len(ancestor_lists)
        return 'a' + str(ancestor_lists[ancestors])

    def state_literal(state):
        frames, initial, terminal = state
        pending_text = ', '.join('⟨' + str(fuel) + ', ' + leaf(item) + ', ' +
                                 path_name(path) + ', ' + ancestors_name(ancestors) + '⟩'
                                 for fuel, item, path, ancestors in frames)
        starts_text = ', '.join('(' + path_name(path) + ', ' + str(index) + ')'
                                for path, index in initial)
        leaves_text = ', '.join('(' + path_name(path) + ', ' +
                                json.dumps(op, ensure_ascii=True) + ')'
                                for path, op in terminal)
        return '⟨[' + pending_text + '], ⟨#[' + starts_text + '], #[' + leaves_text + ']⟩⟩'

    # Assign names in first-occurrence order; this is deterministic in Python 3.7+.
    state_literals = {index: state_literal(value) for index, value in snapshots.items()}
    destination = args.output_directory
    destination.mkdir(parents=True, exist_ok=True)

    def write(module, imports, body):
        text = ''.join('import ' + name + '\n' for name in imports)
        text += ('\n/-! Generated expansion certificate. It concerns the literal Lean AST;\n'
                 'it does not prove the JSON-to-AST or Python algorithm correspondence. -/\n')
        text += 'namespace ' + NAMESPACE + '\nset_option maxRecDepth 8192\n\n'
        text += body
        text += '\nend ' + NAMESPACE + '\n'
        (destination / (module + '.lean')).write_text(text)

    body = ''.join(f'def p{index} : Path := {boolean_list(path)}\n'
                   for path, index in paths.items())
    body += ''.join(f'def a{index} : List Nat := {natural_list(values)}\n'
                    for values, index in ancestor_lists.items())
    write('Paths', ['Shared.Beeping.NPcoNP.Grammar284Data',
                    'Shared.Beeping.NPcoNP.GrammarExpandChunks'], body)
    keys = list(snapshots)
    assert keys == list(range(0, 551, 10)) + [557]
    for stage in range(6):
        low = 100 * stage
        high = min(low + 100, 557)
        imported = PREFIX + ('.Paths' if stage == 0 else f'.Stage{stage-1}')
        local_keys = [k for k in keys if (low <= k <= high if stage == 0 else low < k <= high)]
        body = ''.join(f'def traceState{k} : State := {state_literals[k]}\n' for k in local_keys)
        for start, end in zip(keys, keys[1:]):
            if low <= start < high:
                body += (f'theorem traceChunk{start} : steps producerGrammar.nodes '
                         f'{end-start} traceState{start} = some traceState{end} := by rfl\n')
        write(f'Stage{stage}', [imported], body)

    body = ('theorem producerTrace : steps producerGrammar.nodes 557 traceState0 = '
            'some traceState557 := by\n'
            '  have h10 : steps producerGrammar.nodes 10 traceState0 = some traceState10 := traceChunk0\n')
    for index in range(10, 550, 10):
        body += (f'  have h{index+10} : steps producerGrammar.nodes {index+10} '
                 f'traceState0 = some traceState{index+10} :=\n'
                 f'    chunks producerGrammar.nodes {index} 10 traceState0 traceState{index} '
                 f'traceState{index+10} h{index} traceChunk{index}\n')
    body += ('  exact chunks producerGrammar.nodes 550 7 traceState0 traceState550 '
             'traceState557 h550 traceChunk550\n\n'
             'theorem producerExpand : expand producerGrammar.nodes 53 '
             '(.node producerGrammar.root) [true,true,false] [] {} = some traceState557.acc := by\n'
             '  apply certify producerGrammar.nodes ⟨53, .node producerGrammar.root, '
             '[true,true,false], []⟩ 557 traceState557.acc\n'
             '  change steps producerGrammar.nodes 557 traceState0 = some traceState557\n'
             '  exact producerTrace\n\n'
             'theorem producerStartCount : traceState557.acc.starts.size = 557 := by rfl\n'
             'theorem producerLeafCount : traceState557.acc.leaves.size = 279 := by rfl\n')
    write('Final', [PREFIX + '.Stage5'], body)
    write('Audit', [PREFIX + '.Final'],
          '#print axioms producerTrace\n#print axioms producerExpand\n'
          '#print axioms producerStartCount\n#print axioms producerLeafCount\n')
    print(f'{step} steps, {len(starts)} starts, {len(leaves)} leaves; '
          f'{len(paths)} paths, {len(ancestor_lists)} ancestor lists')


if __name__ == '__main__':
    main()
