"""Paid literal half/parity operation on one unary register block.

The operation returns through the ordinary success path iff the input is odd.
It uses a separate old-ABI selector, leaving the shared INC/DECNZ selector and
its bootstrap adapter unchanged.  All native operands are placed first in the
physical bank; that finite static permutation is part of this producer.
"""
PREFIX = '2h.native_half.'
TAG = '$native-half:'


def operation(register):
    return '3.'+TAG+str(register)+'.decnz'


def operand(operation_name):
    if operation_name.startswith('3.'+TAG) and operation_name.endswith('.decnz'):
        return operation_name[2+len(TAG):-len('.decnz')]
    return None


def kernel_rows():
    rows = {}
    def put(name, read, write, direction, target):
        rows[PREFIX+name, str(read)] = (str(write), direction,
            target if target.startswith(('2b.', '2c.', '1b.')) else PREFIX+target)
    put('begin', 1, 1, 'R', 'initial')
    put('initial', 0, 0, 'L', '2c.reg.return_1_1')
    # The first input unit is already the temporarily incremented quotient
    # boundary. Do not erase it and immediately restore it via a return state.
    put('initial', 1, 1, 'R', 'first')
    put('boundary', 0, 1, 'R', 'first')
    put('first', 0, 0, 'L', 'undo')
    put('first', 1, 0, 'R', 'second')
    put('undo', 1, 0, 'R', '2b.reg.dec.scan_1')
    put('second', 0, 0, 'R', 'even.scan_2')
    put('second', 1, 0, 'R', 'cycle.scan_1')
    for variant, destination in [('cycle', PREFIX+'cycle.return'),
                                 ('even', '2c.reg.return_1_1')]:
        def v(name): return variant+'.'+name
        put(v('scan_1'), 1, 1, 'R', v('scan_1'))
        put(v('scan_1'), 0, 0, 'R', v('scan_2'))
        put(v('scan_2'), 1, 1, 'R', v('scan_1'))
        put(v('scan_2'), 0, 0, 'L', v('shift_1'))
        put(v('shift_1'), 1, 1, 'L', v('shift_1'))
        put(v('shift_1'), 0, 1, 'L', v('shift_2'))
        put(v('shift_2'), 1, 0, 'L', v('shift_1'))
        rows[PREFIX+v('shift_2'), '0'] = ('0', 'L', destination)
    put('cycle.return', 1, 1, 'R', 'boundary')
    put('cycle.return', 0, 0, 'R', '2b.reg.dec.scan_1')
    return rows


def install(builder):
    import tm
    registers = tuple(builder.registers.values())
    used = tuple(builder.native_half_registers)
    if tuple(registers[:len(used)]) != used:
        raise ValueError('native operand prefix permutation not applied')
    rows = builder.tm.states
    for key, value in kernel_rows().items():
        if key in rows:
            raise ValueError('native runtime namespace collision')
        rows[key] = tm.Transition(*value)
    rows[PREFIX+'prep', '0'] = tm.Transition('0', 'R', '1b.reg.prep_2')
    for index, register in enumerate(used):
        rows[operation(register), '0'] = tm.Transition('1', 'R', PREFIX+'prep')
        rows[operation(register), '1'] = tm.Transition('0', 'R', PREFIX+f'select.{index}')
    for index in range(-1, len(used)):
        q = PREFIX+f'select.{index}'
        target = PREFIX+f'select.{index-1}' if index >= 0 else PREFIX+'begin'
        rows[q, '0'] = tm.Transition('0', 'R', target)
        rows[q, '1'] = tm.Transition('1', 'R', q)
    builder.native_half_runtime_certificate = dict(
        format='np-conp-native-half-runtime-v1', operands=list(map(str, used)),
        operation_names=[operation(register) for register in used],
        entry='ordinary prepared path; native old-ABI gap with one separator zero',
        selected_entry='head at first 1 of block 1^(x+1)',
        result='x <- floor(x/2); success iff x was odd; other blocks unchanged',
        native_kernel_states=len({q for q, _ in kernel_rows()}),
        native_selector_states=len(used)+1,
        native_preparation_states=1,
        native_operation_entries=len(used),
        unbounded='all naturals; each cycle removes two remaining input units')


def permute(builder):
    """Change only the finite register-to-unary-block layout before generation."""
    import tm
    old = tuple(builder.registers.values())
    native = tuple(sorted(builder.native_half_registers, key=str))
    ordered = native + tuple(register for register in old if register not in set(native))
    assert set(old) == set(ordered) and len(old) == len(ordered)
    builder.registers = {str(register): register for register in ordered}
    builder.native_half_registers = native
    for index, register in enumerate(ordered):
        for op, terminal in [('inc', register.inc), ('dec', register.decnz)]:
            q = f'2b.reg.{index}.{op}'
            builder.tm.states[q, '0'] = tm.Transition('0', 'R', f'2b.reg.{index-1}.{op}')
            builder.tm.states[q, '1'] = tm.Transition('1', 'R', q)
            builder.tm.states[terminal, '0'] = tm.Transition('1', 'R', '1b.reg.prep_1')
            builder.tm.states[terminal, '1'] = tm.Transition('0', 'R', q)
    builder.native_bank_permutation = dict(old_order=list(map(str, old)),
        new_order=list(map(str, ordered)),
        old_to_new=[ordered.index(register) for register in old],
        blank_entry='all zero blocks, so the same counted initializer realizes the permuted bank')
