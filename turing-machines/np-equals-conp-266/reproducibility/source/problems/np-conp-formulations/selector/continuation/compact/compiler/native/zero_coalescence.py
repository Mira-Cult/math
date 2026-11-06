"""Coalesce cells only under a checked per-operation zero-partner invariant.

One physical class cell represents the sum of its original logical cells.
Whenever a member is operated on, every other member must be definitely zero.
"""
from copy import copy

import abstract_half
import check_contextual
import half_engine
from bank_projection import digest


def rename_operation(operation, mapping):
    if not operation.startswith('3.'):
        return operation
    half = half_engine.operand(operation)
    if half is not None:
        return half_engine.operation(mapping[half])
    name, kind = operation[2:].rsplit('.', 1)
    if kind not in ('inc', 'decnz'):
        raise ValueError('unknown primitive in coalescence')
    return '3.'+mapping[name]+'.'+kind


def invariant_certificate(builder, grammar, data):
    """Use the native no-search checker on an identity contextual rewrite."""
    certificate = dict(schema='np-conp-native-half-contextual-v1',
        domain='all-zero source entry, after the separately verified blank bootstrap',
        event_scope='ordered events and retained register operations preserved; primitive and physical times may change',
        input_grammar=grammar, input_grammar_sha256=digest(grammar),
        output_grammar_sha256=digest(grammar),
        states_at_occurrences=[None if state is None else ''.join(map(str, state))
                              for state in data['states']], zero_rows=[],
        target_nodes=grammar['nodes'], target_root=grammar['root'],
        node_images=[{'node': index} for index in range(len(grammar['nodes']))],
        rewrite_rules=['pair']*len(grammar['nodes']))
    certificate['replay'] = check_contextual.check(builder, builder, certificate)
    return certificate


def coalesce(builder, *, groups=None):
    import tm
    from TMBuilder import TMBuilder
    from build_baseline import grammar
    from live_registers import colour
    import weak_grammar
    before = grammar(builder)
    old = list(builder.registers)
    indices = {name: index for index, name in enumerate(old)}
    _, _, _, data = abstract_half.analyze(builder)
    invariant = invariant_certificate(builder, before, data)
    edges = {name: set() for name in old}
    reached_operations = []
    for index, (state, (_, operation, _, _)) in enumerate(zip(data['states'], data['occurrences'])):
        if state is None or not operation.startswith('3.'):
            continue
        name = half_engine.operand(operation) or operation[2:].rsplit('.', 1)[0]
        reached_operations.append((index, name))
        for other, mask in zip(old, state):
            if other != name and mask != 1:
                edges[name].add(other)
                edges[other].add(name)
    if groups is None:
        colours = colour(edges, old, mode='dsatur')
        groups = [[name for name in old if colours[name] == slot]
                  for slot in sorted(set(colours.values()))]
    else:
        groups = [list(group) for group in groups]
    flat = [name for group in groups for name in group]
    if any(not group for group in groups) or len(flat) != len(old) or set(flat) != set(old):
        raise ValueError('coalescence groups must partition the original carrier')
    aliases = {name: f'$coalesced.{index}' for index, group in enumerate(groups) for name in group}
    peers = {name: group for group in groups for name in group}
    obligations = []
    for index, name in reached_operations:
        state = data['states'][index]
        others = [other for other in peers[name] if other != name]
        if any(state[indices[other]] != 1 for other in others):
            raise ValueError(('nonzero coalescence partner', index, name, others))
        if others:
            obligations.append(dict(occurrence=index, operation_register=name, zero_partners=others))
    native_old = list(map(str, getattr(builder, 'native_half_registers', ())))
    native_new = list(dict.fromkeys(aliases[name] for name in native_old))
    physical = native_new + [f'$coalesced.{index}' for index in range(len(groups))
                             if f'$coalesced.{index}' not in native_new]
    original_graph = weak_grammar.core_graph(builder)
    reached = set(builder.reachable())
    for index in reached:
        sequence = builder.sequences[index]
        sequence.seq = tuple(rename_operation(value, aliases) if isinstance(value, str) else value
                             for value in sequence.seq)
    # Identical renamed pairs can share a physical control state. This changes
    # neither ordered primitive occurrences nor either conditional successor.
    weak_grammar.grammar.normalize(builder)
    mapped_graph = dict(entry=original_graph['entry'], rows=[
        (rename_operation(row[0], aliases), *row[1:]) for row in original_graph['rows']])
    assert weak_grammar.core_graph(builder) == mapped_graph
    builder.tm, builder.registers, builder.nextreg = tm.TuringMachine(), {}, 0
    for name in physical:
        TMBuilder.reg(builder, name)
    if hasattr(builder, 'native_half_registers'):
        builder.native_half_registers = tuple(builder.registers[name] for name in native_new)
    after = grammar(builder)
    builder.pre_coalescence_grammar = before
    builder.coalescence_invariant = invariant
    builder.bank_coalescence_certificate = dict(
        format='np-conp-zero-partner-coalescence-v1',
        domain='all-zero source entry; post-control and post-projection carrier',
        original_register_order=old, physical_register_order=physical,
        groups={f'$coalesced.{index}': group for index, group in enumerate(groups)},
        mapping=aliases, native_operand_order=native_new,
        before_grammar_sha256=digest(before), after_grammar_sha256=digest(after),
        invariant_sha256=digest(invariant), obligations=obligations,
        all_reached_operations_checked=len(reached_operations),
        interference={name: sorted(edges[name]) for name in old},
        original_core_graph_sha256=digest(original_graph),
        mapped_core_graph_sha256=digest(mapped_graph),
        retained_primitives=len(mapped_graph['rows']),
        representation='each physical class cell equals the sum of its old logical cells',
        observation='old logical cells are ghost values, not unconditional aliases of the physical cell',
        progress='same retained primitive sequence and branch outcomes; finite physical primitive execution')
    return builder.bank_coalescence_certificate


class ZeroCoalescenceMixin:
    def generate(self):
        from bank_projection import project
        project(self)
        coalesce(self, groups=getattr(self, 'coalescence_groups', None))
        return super().generate()
