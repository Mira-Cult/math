"""Price operation-specific address chains without the shared tape-mode ABI.

At twelve fields, the shared selector's mode recovery and bootstrap adapters
can cost more than a second indexed chain.  The unchanged inherited runtime
already supplies both chains.  This context validates that complete input and
retains it instead of applying the shared-selector representation change.
"""
from contextlib import contextmanager


@contextmanager
def installed():
    import shared_selector
    from backend import totalize_silently
    original=shared_selector.apply
    def retain(builder):
        registers,depth,paths=shared_selector.check_input(builder)
        rows=builder.tm.states
        entries=[]
        for i,register in enumerate(registers):
            for kind,terminal in [('inc',register.inc),('dec',register.decnz)]:
                assert tuple(rows[terminal,'0'])==('1','R','1b.reg.prep_1')
                assert tuple(rows[terminal,'1'])==('0','R',f'2b.reg.{i}.{kind}')
                entries.append(dict(register=str(register),index=i,operation=kind,terminal=terminal))
        missing=totalize_silently(builder)
        builder.tm.gc()
        return dict(kind='np-conp-control-mode-selector-v1',registers=len(registers),
            source='complete pinned inherited runtime after fresh native allocation/coalescence',
            operation_entries=entries,
            entry='clean h reads0 and prepares; prepared h reads1, clears h and selects control-coded mode/index',
            preparation='one zero at h+1, ones from h+2 through bank anchor',
            operation_information='INC or DECNZ remains in the selected finite chain; no tape mode bit',
            address_information='entry into the fully paid decreasing field-distance chain',
            selector='one chain per operation, with separate inherited INC/DECNZ suffixes',
            bootstrap='original entries and one-zero ABI retained; no mode adapters',
            max_leaf_path=max(len(path) for path,_ in paths),
            old_dispatch_depth=depth,new_dispatch_depth=depth,
            new_totalized_rows=sorted(missing),
            domain='ordinary clean unary-bank primitive occurrences plus separately checked blank startup',
            event_scope='same source events; positive finite segment refinement; physical times differ')
    shared_selector.apply=retain
    try:yield
    finally:shared_selector.apply=original
