"""Conservative source-liveness allocation before primitive grammar factoring.

This is a new compiler continuation.  It does not modify its inherited compiler
or assume bounded source values.  The allocation certificate includes the full
finite source CFG, its liveness fixed point, interference graph and colouring.
Only source-owned registers and their return slots are coalesced.  Return slots
are definitions at explicit returns and observations at procedure exit.
Compiler temporaries and shared arithmetic scratch retain separate storage.
"""
from __future__ import annotations

import ast
from contextlib import contextmanager
from itertools import combinations


def reads(node):
    """All value reads, including every call argument but excluding callee names."""
    if node is None:
        return set()
    if isinstance(node, ast.Name):
        return {node.id} if isinstance(node.ctx, ast.Load) else set()
    if isinstance(node, ast.Call):
        if not isinstance(node.func, ast.Name) or node.keywords:
            raise ValueError('only inherited positional direct calls are supported')
        return set().union(*(reads(arg) for arg in node.args)) if node.args else set()
    return set().union(*(reads(child) for child in ast.iter_child_nodes(node)))


def targets(node):
    if isinstance(node, ast.Name):
        return {node.id}
    if isinstance(node, ast.Tuple) and all(isinstance(x, ast.Name) for x in node.elts):
        names = [x.id for x in node.elts]
        # The inherited frontend accepts repeated tuple targets, but a whole
        # statement definition set would obscure their intermediate writes.
        if len(names) != len(set(names)):
            raise ValueError('repeated tuple target is outside allocation contract')
        return set(names)
    raise ValueError('unsupported allocation target')


def function_cfg(function, return_names=()):
    """Construct explicit statement-boundary control flow, including backedges."""
    nodes = []

    def add(kind, uses=(), defines=(), successors=(), line=0):
        index = len(nodes)
        nodes.append(dict(kind=kind, uses=sorted(uses), defines=sorted(defines),
                          successors=list(successors), line=line))
        return index

    terminal = add('exit', uses=return_names)

    def block(statements, after, loop=None):
        entry = after
        for node in reversed(statements):
            line = getattr(node, 'lineno', 0)
            if isinstance(node, ast.Assign):
                if len(node.targets) != 1:
                    raise ValueError('chained assignment is outside allocation contract')
                entry = add('assign', reads(node.value), targets(node.targets[0]), [entry], line)
            elif isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                entry = add('augment', reads(node.value) | {node.target.id},
                            {node.target.id}, [entry], line)
            elif isinstance(node, ast.If):
                yes, no = block(node.body, entry, loop), block(node.orelse, entry, loop)
                entry = add('if', reads(node.test), successors=[yes, no], line=line)
            elif isinstance(node, ast.While):
                if node.orelse:
                    raise ValueError('while else is outside allocation contract')
                guard = add('while', reads(node.test), line=line)
                body = block(node.body, guard, (entry, guard))
                # Retaining an impossible false edge only adds interference.
                nodes[guard]['successors'] = [body, entry]
                entry = guard
            elif isinstance(node, (ast.Break, ast.Continue)):
                if loop is None:
                    raise ValueError('loop control outside loop')
                entry = add(type(node).__name__.lower(),
                            successors=[loop[isinstance(node, ast.Continue)]], line=line)
            elif isinstance(node, ast.Return):
                entry = add('return', reads(node.value), defines=return_names,
                            successors=[terminal], line=line)
            elif isinstance(node, ast.Expr):
                if isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                    continue
                if not (isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name)
                        and node.value.func.id == 'beep' and not node.value.args
                        and not node.value.keywords):
                    raise ValueError('unsupported allocation expression statement')
                entry = add('beep', successors=[entry], line=line)
            else:
                raise ValueError('unsupported allocation statement: ' + ast.dump(node))
        return entry

    entry = block(function.body, terminal)
    live_in, live_out = [set() for _ in nodes], [set() for _ in nodes]
    changed = True
    while changed:
        changed = False
        for index in range(len(nodes)):
            node = nodes[index]
            out = set().union(*(live_in[x] for x in node['successors']))
            before = set(node['uses']) | (out - set(node['defines']))
            if before != live_in[index] or out != live_out[index]:
                live_in[index], live_out[index] = before, out
                changed = True
    for node, before, after in zip(nodes, live_in, live_out):
        node['live_in'], node['live_out'] = sorted(before), sorted(after)
    return dict(entry=entry, exit=terminal, nodes=nodes)


def interference(function, registers, returns, retained_resets, reuse_returns):
    cfg = function_cfg(function, returns)
    variables = {name for name in registers if name not in returns}
    graph = {name: set() for name in registers}

    def edge(left, right):
        if left != right and left in graph and right in graph:
            graph[left].add(right)
            graph[right].add(left)

    def clique(names):
        for left, right in combinations(sorted(set(names) & set(graph)), 2):
            edge(left, right)

    for node in cfg['nodes']:
        clique(node['live_in'])
        clique(node['live_out'])
        clique(node['defines'])
        for defined in node['defines']:
            for live in node['live_out']:
                edge(defined, live)
    parameters = {a.arg for a in function.args.args}
    clique(parameters)
    # The caller installs every parameter, then the callee performs retained
    # entry resets before the first source statement.  Even a reset for a dead
    # local must not erase a live parameter or another required entry zero.
    entry_live = set(cfg['nodes'][cfg['entry']]['live_in'])
    clique(parameters | entry_live | set(retained_resets))
    # All return expressions have been evaluated into separate temporaries
    # before any return slot is overwritten.  Explicit returns therefore kill
    # the previous slot values.  A possible fallthrough instead keeps its
    # entry-initialized zero return slots live, as the exit uses propagate back.
    clique(returns)
    if not reuse_returns:
        for result in returns:
            for other in registers:
                edge(result, other)
    return cfg, graph


def colour(graph, order, mode='dsatur'):
    if mode not in ('dsatur', 'degree', 'source'):
        raise ValueError(mode)
    rank = {name: index for index, name in enumerate(order)}
    result = {}
    while len(result) != len(graph):
        available = [name for name in graph if name not in result]
        if mode == 'dsatur':
            key = lambda name: (len({result[x] for x in graph[name] if x in result}),
                                len(graph[name]), -rank[name])
        elif mode == 'degree':
            key = lambda name: (len(graph[name]), -rank[name])
        else:
            key = lambda name: (-rank[name],)
        name = max(available, key=key)
        forbidden = {result[x] for x in graph[name] if x in result}
        slot = 0
        while slot in forbidden:
            slot += 1
        result[name] = slot
    return result


def check_function_certificate(certificate):
    """Replay graph constraints and fixed-point equations without search."""
    cfg, graph, colours = (certificate[key] for key in ('cfg', 'graph', 'colours'))
    nodes = cfg['nodes']
    assert set(graph) == set(colours)
    assert 0 <= cfg['entry'] < len(nodes) and 0 <= cfg['exit'] < len(nodes)

    def require_edge(left, right):
        if left != right and left in graph and right in graph:
            assert right in graph[left] and left in graph[right]

    def require_clique(names):
        for left, right in combinations(sorted(set(names) & set(graph)), 2):
            require_edge(left, right)

    for index, node in enumerate(nodes):
        assert all(type(x) is int and 0 <= x < len(nodes) for x in node['successors'])
        out = set().union(*(set(nodes[x]['live_in']) for x in node['successors']))
        assert out == set(node['live_out'])
        assert set(node['live_in']) == set(node['uses']) | (out - set(node['defines']))
        require_clique(node['live_in'])
        require_clique(node['live_out'])
        require_clique(node['defines'])
        for defined in node['defines']:
            for live in node['live_out']:
                require_edge(defined, live)
    require_clique(certificate['parameters'])
    require_clique(set(certificate['parameters']) | set(certificate['retained_resets'])
                   | set(nodes[cfg['entry']]['live_in']))
    require_clique(certificate['returns'])
    for left, neighbours in graph.items():
        assert left not in neighbours
        for right in neighbours:
            assert left in graph[right]
            assert colours[left] != colours[right]
    assert all(type(value) is int and value >= 0 for value in colours.values())


def pool_frames(builder, *, mode='dsatur', reuse_returns=True):
    """Allocate local lifetimes and preserve inherited call-height separation."""
    from frame_pool import source_owners
    from TMBuilder import TMBuilder
    import tm

    logical_registers = list(builder.registers)
    owners = source_owners(builder, logical_registers)
    mapping = {name: name for name in logical_registers}
    certificates, sizes = {}, {}
    for name, frame in builder.frames.items():
        owned = [register for register in logical_registers if owners.get(register) == name]
        local_order = [register[len(name) + 1:] for register in owned]
        returns = [str(register)[len(name) + 1:] for register in frame['returns']]
        retained = [register[len(name) + 1:] for register in
                    builder.assignment_certificates[name]['retained_entry_resets']]
        cfg, graph = interference(builder.functions[name], local_order, returns, retained, reuse_returns)
        colours = colour(graph, local_order, mode)
        certificate = dict(cfg=cfg, graph={k: sorted(v) for k, v in sorted(graph.items())},
                           colours=colours, parameters=list(frame['args']),
                           returns=returns, retained_resets=retained)
        check_function_certificate(certificate)
        certificates[name] = certificate
        sizes[name] = max(colours.values(), default=-1) + 1
        for register, local in zip(owned, local_order):
            mapping[register] = f'$liveframe.{builder.heights[name]}.{colours[local]}'
    # Check direct call-height separation afresh; no recursive frame aliases.
    for name in builder.frames:
        for node in ast.walk(builder.functions[name]):
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id in builder.frames):
                assert builder.heights[node.func.id] < builder.heights[name]
    physical_order = list(dict.fromkeys(mapping.values()))
    assert len(set(mapping)) == len(logical_registers)
    for sequence in builder.sequences:
        renamed = []
        for value in sequence.seq:
            if isinstance(value, str) and value.startswith('3.'):
                register, operation = value[2:].rsplit('.', 1)
                value = '3.' + mapping[register] + '.' + operation
            renamed.append(value)
        sequence.seq = tuple(renamed)
    builder.tm, builder.registers, builder.nextreg = tm.TuringMachine(), {}, 0
    for physical in physical_order:
        TMBuilder.reg(builder, physical)
    builder.logical_to_physical = mapping
    builder.logical_registers = logical_registers
    builder.frame_pool_certificate = dict(
        format='source-liveness-allocation-v1', mode=mode, reuse_returns=reuse_returns,
        heights={name: builder.heights[name] for name in sorted(builder.frames)},
        frame_sizes=sizes, logical_registers=len(logical_registers),
        physical_registers=len(physical_order), mapping=mapping, functions=certificates)
    return builder


@contextmanager
def allocated_runtime(mode='dsatur', reuse_returns=True):
    """Scope the new pass; inherited producer bytes and global hooks are restored."""
    import frame_pool
    original = frame_pool.pool_frames
    frame_pool.pool_frames = lambda builder: pool_frames(builder, mode=mode, reuse_returns=reuse_returns)
    try:
        yield
    finally:
        frame_pool.pool_frames = original
