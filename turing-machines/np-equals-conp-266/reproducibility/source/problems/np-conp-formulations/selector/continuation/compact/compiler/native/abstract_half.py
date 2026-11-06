"""Zero/one/many analysis with a proved half/parity primitive transfer."""
from collections import defaultdict, deque

from half_engine import operand as native_operand


def analyze(builder):
    root = builder.find_seq('main().0')
    nodes = tuple(tuple(sequence.seq) for sequence in builder.sequences)
    registers = tuple(builder.registers)
    indices = {str(register): index for index, register in enumerate(registers)}
    occurrences = []
    def unfold(item, path, parent=None, bit=None):
        if type(item) is int:
            for child_bit, child in enumerate(nodes[item]):
                unfold(child, path+str(child_bit), item, child_bit)
        else:
            occurrences.append((path, str(item), parent, bit))
    unfold(root, '110')
    by_path = {path: index for index, (path, *_) in enumerate(occurrences)}
    def resolve(path):
        if path.startswith('111'): path = '110'
        if len(path) < 3: path += '0'*(3-len(path))
        node, index = root, 3
        while type(node) is int:
            if index == len(path): path += '0'
            node = nodes[node][int(path[index])]
            index += 1
        assert index == len(path)
        return by_path[path]
    def ret(path, skip):
        for index in range(len(path)-1, 1, -1):
            if path[index] == '0':
                if skip: skip -= 1
                else: return resolve(path[:index]+'1')
        raise ValueError('return beyond root')
    def restart(path, skip):
        for index in range(len(path)-1, 0, -1):
            if path[index] == '1':
                if skip: skip -= 1
                else: return resolve(path[:index+1])
        raise ValueError('continue beyond root')
    edges = []
    for path, operation, _, _ in occurrences:
        if operation.startswith('_break.'):
            out = [(ret(path, int(operation.split('.')[1])), None, None)]
        elif operation.startswith('_continue.'):
            out = [(restart(path, int(operation.split('.')[1])), None, None)]
        elif operation == 'beep':
            out = [(ret(path, 0), None, None)]
        else:
            name, kind = operation[2:].rsplit('.', 1)
            half = native_operand(operation)
            slot = indices[half or name]
            if half is not None:
                out = [(ret(path, 0), slot, 'odd-half'), (ret(path, 1), slot, 'even-half')]
            elif kind == 'inc':
                out = [(ret(path, 0), slot, 'inc')]
            else:
                assert kind == 'decnz'
                out = [(ret(path, 0), slot, 'positive'), (ret(path, 1), slot, 'zero')]
        edges.append(out)
    states = [None]*len(occurrences)
    start = resolve('110')
    states[start] = [1]*len(registers)
    work = deque([start])
    iterations = 0
    while work:
        index = work.popleft()
        state = states[index]
        iterations += 1
        for destination, slot, operation in edges[index]:
            out = state.copy()
            if operation == 'inc':
                out[slot] = (2 if state[slot]&1 else 0)|(4 if state[slot]&6 else 0)
            elif operation in ('positive', 'odd-half'):
                if not state[slot]&6: continue
                out[slot] = (1 if state[slot]&2 else 0)|(6 if state[slot]&4 else 0)
            elif operation == 'zero':
                if not state[slot]&1: continue
                out[slot] = 1
            elif operation == 'even-half':
                if not state[slot]&5: continue
                out[slot] = (1 if state[slot]&1 else 0)|(6 if state[slot]&4 else 0)
            previous = states[destination]
            merged = out if previous is None else [a|b for a, b in zip(previous, out)]
            if previous != merged:
                states[destination] = merged
                work.append(destination)
    groups, zero = defaultdict(list), set()
    for index, (_, operation, parent, bit) in enumerate(occurrences):
        if states[index] is None: continue
        groups[parent, bit].append(index)
        if operation.endswith('.decnz'):
            name = native_operand(operation) or operation[2:].rsplit('.', 1)[0]
            if states[index][indices[name]] == 1: zero.add(index)
    replacements = {key: '_break.1' for key, invocations in groups.items()
                    if all(index in zero for index in invocations)}
    live = set()
    for index, (path, *_) in enumerate(occurrences):
        if states[index] is None: continue
        node = root
        for digit in path[3:]:
            live.add((node, int(digit)))
            node = nodes[node][int(digit)]
    summary = dict(occurrences=len(occurrences), reachable=sum(state is not None for state in states),
        zero_occurrences=len(zero), all_context_zero_groups=len(replacements),
        dead_grammar_rows=2*len(tuple(builder.reachable()))-len(live), iterations=iterations)
    return summary, replacements, live, dict(occurrences=occurrences, states=states, edges=edges, root=root)
