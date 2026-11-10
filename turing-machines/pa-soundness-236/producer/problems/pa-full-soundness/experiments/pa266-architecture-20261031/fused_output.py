#!/usr/bin/env python3
"""Emit at the final grammar branch and use its existing clean continuation.

An output leaf has no register-bank action. Its parent row can emit the bit
and perform the ordinary break.0 continuation directly, eliminating both
standalone output states. The event convention itself is unchanged.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib
import json
import sys
from collections import Counter
from pathlib import Path
import total_preparation
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'architecture'))
import clean_rebind
p=clean_rebind.p


class FusedOutput:
    def generate(self):
        super().generate()
        self.fused_event_labels={}
        for index in self.reachable():
            sequence=self.sequences[index]
            for read,child in enumerate(sequence.seq):
                if child not in ('emit.0','emit.1'):
                    continue
                bit=child[-1]
                target='6.continue.0' if read==0 else '6.break.0'
                self.tm.states[sequence.name,str(read)]=p.opt.tm.Transition(
                    str(1-read),'L',target)
                self.fused_event_labels[sequence.name,str(read)]=bit
        assert self.fused_event_labels


class FusedClean(FusedOutput,clean_rebind.ReboundClean):
    pass


def compile_candidate(cls,out):
    """Count complete event-labelled rows, then compute their exact quotient."""
    out=Path(out)
    builder=cls(p.opt.SOURCE);builder.build_tree();builder.generate()
    labels=builder.fused_event_labels
    initial=p.opt.build.counted_initializer(builder)
    builder.tm.symbols={'0','1'};builder.tm.gc()
    missing=p.opt.totalize_silently(builder);builder.tm.gc()
    named={(q,int(r)):(int(t.write),t.direction,t.nextstate,labels.get((q,r),'-'))
           for (q,r),t in builder.tm.states.items()}
    assert not any(q.startswith('emit.') for q,_ in named)
    root,measures=p.opt.build.dag_measures(builder)
    common=dict(initializer=initial,register_order=list(builder.registers),grammar_root=root,
        grammar={str(i):list(builder.sequences[i].seq) for i in sorted(builder.reachable())},
        grammar_names={str(i):builder.sequences[i].name for i in sorted(builder.reachable())},
        grammar_depth=measures[root][0],grammar_zero_depth=measures[root][1],
        totalized_rows=[[q,int(s)] for q,s in sorted(missing)],direct_events=True,
        source_sha256=hashlib.sha256(p.opt.SOURCE.encode()).hexdigest(),
        generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        variant=cls.__name__,canonical_admission=False,
        fused_output_rows=[[q,int(read),bit] for (q,read),bit in sorted(labels.items())],
        run_dispatch=builder.run_dispatch_certificate)
    summaries={};result_rows={}
    assert initial['registers']<=1909 and initial['max_leaf_path']<3822
    for mode,table in [('counted',named),('boot',p.opt.boot_named(named,common['register_order'][0]))]:
        rows,ids=p.opt.build.number_rows(table)
        categories=Counter(('bootstrap' if mode=='boot' else 'initializer') if q.startswith('init.') else
            'grammar' if q in common['grammar_names'].values() else
            'register-selection' if q.startswith(('2b.reg.','3.')) else
            'events' if q.startswith(('event.','emit.')) else 'engine-and-totalization' for q in ids)
        meta=dict(common,named_state_to_id=ids,state_ledger=dict(categories))
        if mode=='boot':meta['entry_geometry']=dict(head=-3818,ones=[-3821,-3820]+list(range(3,3822,2)))
        raw=p.opt.build.write_machine(out/mode/'raw',rows,meta)
        reduced,certificate=p.opt.build.exact_quotient(rows)
        certificate['source_table_sha256']=raw['table_sha256']
        best=p.opt.build.write_machine(out/mode/'quotient',reduced,
            dict(parent='raw',quotient=certificate,variant=cls.__name__,
                source_sha256=common['source_sha256'],generator_sha256=common['generator_sha256']))
        summaries[mode]=dict(raw=raw['states'],selected=best['states'],rows=best['transitions'],
            ledger=dict(categories),sha256=best['table_sha256'],registers=len(builder.registers))
        result_rows[mode]=(rows,reduced,certificate)
    (out/'ledger.json').write_text(json.dumps(summaries,sort_keys=True,indent=2)+'\n')
    (out/'run-dispatch.json').write_text(json.dumps(builder.run_dispatch_certificate,
                                                  sort_keys=True,indent=2)+'\n')
    return builder,summaries,result_rows


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(compile_candidate(FusedClean,args.out)[1],indent=2))
