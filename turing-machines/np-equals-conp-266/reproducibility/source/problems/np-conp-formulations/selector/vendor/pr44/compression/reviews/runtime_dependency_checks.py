"""Independent focused checks for the frozen selector/quotient dependencies.

This is review code, not part of the machine or either producer. It builds the
selected grammar once, validates inherited event/control rows independently,
checks selector joins at the minimum admitted gap, and replays the actual
quotient certificate with its search routines disabled. It does not rerun the
long blank-tape prefixes.
"""
from pathlib import Path
from copy import deepcopy
import hashlib,json,sys

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'compression/compiler'),str(ROOT/'compression'),
             str(ROOT/'compression/source'),str(ROOT/'shared')]
import contextual_tree_build,integrated_build,shared_selector
import contextual_quotient as producer
from check_contextual_quotient import check as check_contextual
from build_baseline import canonicalize
from backend import totalize_silently
from machine import parse
from test_natural import assert_factorable_entries_closed
from test_occurrences import paths
import tm


def table(builder):
    return {(q,int(b)):(int(t.write),-1 if t.direction=='L' else 1,t.nextstate)
            for (q,b),t in builder.tm.states.items()}


def check_inherited_families(builder):
    """Check the row families outside the selector's fixed-framework guard."""
    rows=table(builder)
    expected={
        ('beep',0):(1,1,'1b.reg.prep_1'),('beep',1):(0,-1,'B'),
        ('B',0):(1,1,'2e.reg.cleanup_1'),('B',1):(0,-1,'6.break.0')}
    inventory={kind:sorted({int(q.rsplit('.',1)[1]) for q,b in rows
                           if q.startswith('6.'+kind+'.')})
               for kind in ('break','continue')}
    for kind,levels in inventory.items():
        if not levels or levels!=list(range(max(levels)+1)):
            raise ValueError('control inventory '+kind)
        for k in levels:
            if not k:continue
            q=f'6.{kind}.{k}'
            expected[q,0]=(0,-1,f'6.break.{k-1}' if kind=='break' else q)
            expected[q,1]=(0,-1,q if kind=='break' else f'6.continue.{k-1}')
    expected['6.break.0',0]=(1,1,'2e.reg.cleanup_1')
    expected['6.break.0',1]=(0,-1,'6.break.0')
    expected['6.continue.0',0]=(0,-1,'6.continue.0')
    depth=max(path.count(0) for path,_,_ in paths(builder))+1
    if any(q.startswith('shared.selector.') for q,b in rows):depth+=1
    expected['6.continue.0',1]=(1,-1,f'4.dispatch.{depth}')
    for key,wanted in expected.items():
        if rows.get(key)!=wanted:raise ValueError(('inherited row',key,rows.get(key),wanted))
    # Every lexical leaf's needed inherited tail must actually be represented.
    for path,leaf,_ in paths(builder):
        op=str(leaf);bit=path[-1]
        if op.startswith('_break.'):
            k=int(op.split('.')[1]);target=0 if k==0 and bit==0 else k-(bit==0)
            if target not in inventory['break']:raise ValueError('missing break tail')
        elif op.startswith('_continue.'):
            if int(op.split('.')[1])-bit not in inventory['continue']:
                raise ValueError('missing continuation tail')
    return {'rows_checked':len(expected),'control_levels':inventory,
            'dispatch_depth':depth}


def encoded(path,anchor,values,offset=0,prepared=False):
    ones={i+offset for i,x in enumerate(path) if x}
    ones.add(anchor+offset);cursor=anchor+2
    starts=[]
    for value in values:
        starts.append(cursor+offset)
        ones.update(range(cursor+offset,cursor+offset+value+1));cursor+=value+2
    if prepared:
        ones.add(len(path)+offset)
        ones.update(range(len(path)+2+offset,anchor+offset+1))
    return ones,starts


def advance_to_join(rows,state,head,ones,join,limit=200000):
    tape=set(ones)
    for count in range(limit):
        if (state,head)==join:return count,tape
        if state in ('B','silent.sink'):raise AssertionError(('unwanted event/sink',state))
        write,move,target=rows[state,int(head in tape)]
        if write:tape.add(head)
        else:tape.discard(head)
        state=target;head+=move
    raise AssertionError('selector join fuel')


def selector_joins(before,after):
    old,new=table(before),table(after);regs=tuple(before.registers)
    occurrences=list(paths(before));records=[]
    for index in (0,len(regs)//2,len(regs)-1):
        for operation in ('inc','decnz'):
            op='3.'+str(regs[index])+'.'+operation
            candidates=[p for p,leaf,_ in occurrences if str(leaf)==op]
            if not candidates:raise AssertionError(('missing tested primitive',op))
            path=max(candidates,key=len);anchor=len(path)+3
            for value in (0,1,2,37,257):
                for reserves in (0,3):
                    values=[(2*i+value)%7 for i in range(len(regs))]+[0]*reserves
                    values[index]=value
                    for offset in (-29,0,31):
                        for prepared in (False,True):
                            tape,starts=encoded(path,anchor,values,offset,prepared)
                            # Old/new prepared layouts differ at the extra zero.
                            new_tape=set(tape)
                            if prepared:new_tape.discard(len(path)+2+offset)
                            join=('2b.reg.-2.inc' if operation=='inc' else '2b.reg.dec.check',starts[index]+1)
                            nold,told=advance_to_join(old,op,len(path)+offset,tape,join)
                            nnew,tnew=advance_to_join(new,op,len(path)+offset,new_tape,join)
                            if told!=tnew:raise AssertionError(('join tape mismatch',index,operation,value,prepared))
                            records.append(dict(register=index,operation=operation,value=value,
                                reserves=reserves,translation=offset,entry='prepared' if prepared else 'clean',
                                gap=3,old_transitions=nold,new_transitions=nnew,
                                joined_tape_sha256=hashlib.sha256(json.dumps(sorted(tnew)).encode()).hexdigest()))
    return records


def run():
    source=ROOT/'compression/source/source_head_stream.py'
    b=contextual_tree_build.SelectedContextualTreeBuilder(source.read_text(),
        fused_consuming=True,compact_equal=True,countdown_division=True,
        refactor_options={'scoring':'prefer-right'},shared_selector=False,
        intrinsic_sites=integrated_build.parity_sites(source.read_text()),**integrated_build.OPTIONS)
    b.main();assert_factorable_entries_closed(b);b.build_machine()
    shared_selector.check_input(b)
    inherited_before=check_inherited_families(b)
    # Demonstrate the existing guard boundary without misclassifying it as a
    # failure of the stated unchanged-runtime precondition.
    guard_boundary=[];independent_rejections=[]
    for key in (('beep','0'),('B','1'),('6.break.2','0'),('6.continue.1','1')):
        changed=deepcopy(b);row=changed.tm.states[key]
        changed.tm.states[key]=tm.Transition('1' if row.write=='0' else '0',row.direction,row.nextstate)
        shared_selector.check_input(changed)
        guard_boundary.append(key)
        try:check_inherited_families(changed)
        except ValueError:independent_rejections.append(key)
        else:raise AssertionError(('independent guard missed mutation',key))
    after=deepcopy(b);selector=shared_selector.apply(after)
    inherited_after=check_inherited_families(after)
    joins=selector_joins(b,after)
    totalize_silently(after);after.tm.gc();raw,names=canonicalize(after)
    folder=ROOT/'compression/machines/horn-570'
    saved_raw=parse(folder/'raw.tm');selected=parse(folder/'machine.tm')
    if raw!=saved_raw:raise AssertionError('selected raw machine changed')
    certificate=json.loads((folder/'contextual-certificate.json').read_text())
    # Replay imports only digests from the producer. Discovery is unavailable.
    old_analyze,old_quotient=producer.analyze,producer.quotient
    def forbidden(*args,**kwargs):raise AssertionError('checker invoked search')
    producer.analyze=producer.quotient=forbidden
    rejected=[]
    try:
        replay=check_contextual(after,raw,selected,names,certificate)
        def reject(label,change):
            bad=deepcopy(certificate);change(bad)
            try:check_contextual(after,raw,selected,names,bad)
            except (ValueError,KeyError,IndexError,AssertionError):rejected.append(label)
            else:raise AssertionError(('accepted certificate mutant',label))
        reject('missing zero entry',lambda c:c['states_at_occurrences'].__setitem__(0,None))
        reject('positive-only entry',lambda c:c['states_at_occurrences'].__setitem__(0,'2'*len(after.registers)))
        reached=[i for i,s in enumerate(certificate['states_at_occurrences']) if s is not None and i]
        reject('removed reachable successor',lambda c:c['states_at_occurrences'].__setitem__(reached[0],None))
        reject('extra ignored bootstrap row',lambda c:c['ignored_rows'].append([raw.start,0]))
        reject('missing mapping source',lambda c:c['mapping'].pop(str(raw.start)))
        reject('event-color merge',lambda c:c['mapping'].__setitem__(str(raw.beep),c['mapping'][str(raw.start)]))
        reject('all-input domain relabel',lambda c:c.update(domain='all configurations'))
        reject('duplicate ignored row',lambda c:c['ignored_rows'].append(c['ignored_rows'][0]))
        weak=deepcopy(certificate)
        weak.update(states_at_occurrences=['7'*len(after.registers)]*len(weak['states_at_occurrences']),
            ignored_grammar_rows=[],ignored_rows=[],mapping={q:q for q in range(raw.count)},
            table_sha256=producer.machine_digest(raw))
        weak_replay=check_contextual(after,raw,raw,names,weak)
    finally:producer.analyze,producer.quotient=old_analyze,old_quotient
    files=['compression/compiler/shared_selector.py','compression/compiler/contextual_quotient.py',
           'compression/compiler/check_contextual_quotient.py','shared/vendor/TMBuilder.py',
           'shared/backend.py','shared/test_occurrences.py','shared/test_natural.py',
           'compression/compiler/contextual_tree_build.py','compression/integrated_build.py',
           'compression/source/intrinsic_build.py','compression/source/source_head_stream.py',
           'compression/machines/horn-570/machine.tm','compression/machines/horn-570/raw.tm',
           'compression/machines/horn-570/contextual-certificate.json']
    return dict(scope='independent inherited-row, minimum-gap selector join and no-search quotient replay checks; no long blank trace rerun',
        inherited_before=inherited_before,inherited_after=inherited_after,
        existing_selector_guard_unchecked_mutants=guard_boundary,
        additional_validator_rejections=independent_rejections,selector=selector,
        selector_join_cases=len(joins),selector_join_old_transitions=sum(r['old_transitions'] for r in joins),
        selector_join_new_transitions=sum(r['new_transitions'] for r in joins),selector_join_records=joins,
        selected_replay=replay,selected_rejected_certificate_mutants=rejected,
        all_unknown_identity_replay=weak_replay,
        files={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in files},
        review_driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
