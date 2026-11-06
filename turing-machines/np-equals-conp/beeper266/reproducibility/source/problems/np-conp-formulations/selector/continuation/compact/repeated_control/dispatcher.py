"""Replace total-zero countdown by an admitted-path zero-run delimiter.

The tape and the grammar are unchanged.  The left blank margin is the delimiter;
no address, counter or initial tape is supplied for free.  All input runtime rows
are checked before changing only dispatcher states and its unique entry.
"""
from hashlib import sha256
import json


PREFIX = 'repeat.dispatch.'


def longest_zero_run(word):
    return max(map(len, word.split('1')))


def install(builder, *, limit=None):
    import tm
    from backend import leaf_paths
    paths = sorted(leaf_paths(builder))
    assert paths
    # leaf_paths already includes the fixed 110 root header.
    maximum = max(longest_zero_run(path+'100') for path, _ in paths)
    if limit is None:
        limit = maximum+1
    assert type(limit) is int and limit > maximum
    rows = builder.tm.states
    original_entry = tuple(rows['6.continue.0', '1'])
    old_depth = int(original_entry[2].rsplit('.', 1)[1])
    assert original_entry == ('1', 'L', f'4.dispatch.{old_depth}')
    old_rows = {}
    for i in range(old_depth+1):
        q = f'4.dispatch.{i}'
        for bit in ('0','1'):
            target = (f'4.dispatch.{i-1}' if i else '4.dispatch.scan') if bit=='0' else q
            actual = tuple(rows[q, bit])
            assert actual == (bit, 'L', target), (q, bit, actual)
            old_rows[q, bit] = actual
    old_names = {q for q, _ in old_rows}
    ingresses = [(q,bit) for (q,bit),row in rows.items()
                 if row.nextstate in old_names and q not in old_names]
    assert ingresses == [('6.continue.0','1')], ingresses
    for key in old_rows:
        del rows[key]
    for i in range(limit):
        q = PREFIX+str(i)
        assert not any((q,b) in rows for b in ('0','1'))
        rows[q,'0'] = tm.Transition('0','L',PREFIX+str(i+1) if i+1<limit else '4.dispatch.scan')
        rows[q,'1'] = tm.Transition('1','L',PREFIX+'0')
    rows['6.continue.0','1'] = tm.Transition('1','L',PREFIX+'0')
    certificate = dict(format='np-conp-zero-run-dispatch-v1',
        source_geometry='unchanged 110 root/path and unary bank; unchanged preparation',
        terminal_paths=[[p,t] for p,t in paths],
        max_path_zeros=max(p.count('0') for p,_ in paths),
        max_path_length=max(len(p) for p,_ in paths),
        max_prepared_zero_run=maximum, limit=limit,
        old_depth=old_depth, old_dispatcher_states=old_depth+1,
        new_dispatcher_states=limit,
        entry_before=list(original_entry), entry_after=list(rows['6.continue.0','1']),
        old_rows=[[q,int(bit),*value] for (q,bit),value in sorted(old_rows.items())],
        new_rows=[[q,int(bit),*tuple(value)] for (q,bit),value in sorted(rows.items()) if q.startswith(PREFIX)],
        external_ingresses=[list(k) for k in ingresses],
        boundary_relation='same whole tape, head and root state after finite left/right redispatch; timing may differ',
        termination='no zero-run reaches limit between scan entry and root; finite root-left blank margin supplies limit zeros',
        bootstrap='separate fresh literal blank-entry lemma required; ordinary path language is not a bootstrap proof',
        changes_to_source_or_bank=False)
    certificate['path_language_sha256']=sha256(json.dumps(certificate['terminal_paths'],separators=(',',':')).encode()).hexdigest()
    builder.zero_run_dispatch_certificate = certificate
    return certificate
