"""Pool source-frame registers only across nonoverlapping call-graph heights.

The target interface preserves events and active-frame values. Values of
completed, inactive procedure frames are deliberately not observations.
"""
from namespace_safe import NamespaceSafeBuilder
from TMBuilder import TMBuilder
import tm


def source_owners(builder,logical_registers):
    """Use source AST identity, never an internal register's string prefix."""
    import ast
    present=set(logical_registers)
    owners={}
    for name,frame in builder.frames.items():
        function=builder.functions[name]
        runtime=ast.Module(body=function.body,type_ignores=[])
        call_names={id(node.func) for node in ast.walk(runtime)
                    if isinstance(node,ast.Call)}
        names=set(frame['args']) | {node.id for node in ast.walk(runtime)
                                  if isinstance(node,ast.Name) and id(node) not in call_names}
        registers={name+'.'+local for local in names} | {str(r) for r in frame['returns']}
        for register in registers & present:
            if register in owners and owners[register]!=name:
                raise ValueError('conflicting source register ownership')
            owners[register]=name
    assert str(builder.scratch) not in owners
    return owners


def check_mapping(builder, logical_registers, mapping, physical_order):
    assert set(mapping) == set(logical_registers)
    assert set(mapping.values()) == set(physical_order)
    frame_names = set(builder.frames)
    owners = source_owners(builder,logical_registers)
    grouped = {}
    owned = {}
    for logical in logical_registers:
        owner = owners.get(logical)
        if owner is not None:
            grouped.setdefault(owner, []).append(logical)
            owned[logical] = owner
        else:
            assert mapping[logical] == logical
    for name, registers in grouped.items():
        assert len({mapping[x] for x in registers}) == len(registers)
    for i, left in enumerate(logical_registers):
        for right in logical_registers[i+1:]:
            if mapping[left] == mapping[right]:
                assert left in owned and right in owned
                assert owned[left] != owned[right]
                assert builder.heights[owned[left]] == builder.heights[owned[right]]
    # Recheck every direct call edge, not just the arithmetic labels.
    import ast
    for name in frame_names:
        for node in ast.walk(builder.functions[name]):
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                    and node.func.id in frame_names):
                assert builder.heights[node.func.id] < builder.heights[name]


def pool_frames(builder):
    logical_registers = list(builder.registers)
    frame_names = set(builder.frames)
    owners = source_owners(builder,logical_registers)
    indices = {}
    mapping = {}
    for logical in logical_registers:
        owner = owners.get(logical)
        if owner is not None:
            slot = indices.get(owner, 0)
            indices[owner] = slot + 1
            mapping[logical] = f'$frame.{builder.heights[owner]}.{slot}'
        else:
            mapping[logical] = logical
    physical_order = list(dict.fromkeys(mapping.values()))
    check_mapping(builder, logical_registers, mapping, physical_order)
    # Compilation is complete: rename every primitive occurrence before any
    # physical table generation. The original finite control DAG is unchanged.
    for sequence in builder.sequences:
        renamed = []
        for value in sequence.seq:
            if isinstance(value, str) and value.startswith('3.'):
                name, operation = value[2:].rsplit('.', 1)
                value = '3.' + mapping[name] + '.' + operation
            renamed.append(value)
        sequence.seq = tuple(renamed)
    builder.tm = tm.TuringMachine()
    builder.registers = {}
    builder.nextreg = 0
    for physical in physical_order:
        TMBuilder.reg(builder, physical)
    builder.logical_to_physical = mapping
    builder.logical_registers = logical_registers
    builder.frame_pool_certificate = dict(
        heights={name: builder.heights[name] for name in sorted(frame_names)},
        frame_sizes=indices, logical_registers=len(logical_registers),
        physical_registers=len(physical_order), mapping=mapping)
    return builder


class FramePooledBuilder(NamespaceSafeBuilder):
    def build_tree(self):
        super().build_tree()
        return pool_frames(self)
