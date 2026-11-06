"""Remove only registers absent from every retained primitive occurrence.

This is a projection of the all-zero-entry register computation, performed
after contextual/control rewriting and before any physical rows are generated.
The old grammar, full carrier, and explicit zero interpretations are retained.
"""
from hashlib import sha256
import json

from half_engine import operand as native_operand


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def project(builder):
    import tm
    from TMBuilder import TMBuilder
    from build_baseline import grammar
    before = grammar(builder)
    old = tuple(builder.registers.values())
    old_names = set(map(str, old))
    active, native, occurrences = set(), set(), []
    for index, pair in enumerate(before['nodes']):
        for bit, item in enumerate(pair):
            child = item.get('op')
            if child is None or not child.startswith('3.'):
                continue
            half = native_operand(child)
            if half is not None:
                name, kind = half, 'native-half'
                native.add(name)
            else:
                name, kind = child[2:].rsplit('.', 1)
                if kind not in ('inc', 'decnz'):
                    raise ValueError('unknown retained primitive during bank projection')
            if name not in old_names:
                raise ValueError('retained primitive has no allocated register')
            active.add(name)
            occurrences.append(dict(node=index, bit=bit, operation=child,
                                    register=name, kind=kind))
    if not active:
        # TMBuilder's boot contract needs one physical register even for a
        # program that only beeps. Keep its existing first zero register.
        active.add(str(old[0]))
    native_order = tuple(register for register in old if str(register) in native)
    ordinary_order = tuple(register for register in old
                           if str(register) in active and str(register) not in native)
    retained = native_order + ordinary_order
    removed = tuple(register for register in old if str(register) not in active)
    assert len(set(retained)) == len(retained)
    assert set(retained).isdisjoint(removed)
    assert set(retained) | set(removed) == set(old)
    assert all(row['register'] in set(map(str, retained)) for row in occurrences)

    builder.pre_projection_grammar = before
    builder.pre_projection_registers = old
    builder.tm, builder.registers, builder.nextreg = tm.TuringMachine(), {}, 0
    for register in retained:
        TMBuilder.reg(builder, str(register))
    if hasattr(builder, 'native_half_registers'):
        builder.native_half_registers = tuple(builder.registers[str(register)] for register in native_order)
    after = grammar(builder)
    # No primitive name, edge, grammar node or root changes in this pass.
    assert {key: value for key, value in before.items() if key != 'registers'} == {
        key: value for key, value in after.items() if key != 'registers'}
    builder.bank_projection_certificate = dict(
        format='np-conp-unused-zero-bank-projection-v1',
        domain='all-zero source entry after contextual and finite-control rewriting',
        before_grammar_sha256=digest(before), after_grammar_sha256=digest(after),
        original_register_order=list(map(str, old)),
        retained_register_order=list(map(str, retained)),
        removed_registers=list(map(str, removed)),
        removed_interpretation={str(register): 0 for register in removed},
        old_to_new=[retained.index(register) if register in retained else None for register in old],
        retained_primitives=occurrences, native_operand_order=list(map(str, native_order)),
        aliasing='distinct retained cells remain distinct; no value-cell identification',
        physical_rebuild='all original INC/DECNZ index and entry rows regenerated before framework generation',
        contextual_scope='original carrier in pre-control grammar; finite-control scope ends at pre-projection grammar',
        simulation='retained values agree; omitted cells stay zero because no retained operation references them',
        bootstrap='same counted all-zero producer; fresh literal entry required for this complete table')
    return builder.bank_projection_certificate


class BankProjectionMixin:
    def generate(self):
        project(self)
        return super().generate()
