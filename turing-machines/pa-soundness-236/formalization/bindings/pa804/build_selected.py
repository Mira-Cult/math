#!/usr/bin/env python3
"""Rebuild selected faithful PA soundness candidate and its grammar certificate."""
from __future__ import annotations
import argparse,hashlib,json
from pathlib import Path
import optimize as opt
import grammar_search as gs
ROOT=Path(__file__).resolve().parent
PLAN=ROOT/'grammar-plan.json'

class ReassociatedOneStack(gs.FactoredOneStack):
    def build_tree(self):
        super().build_tree()
        plan=json.loads(PLAN.read_text())
        before=gs.graph(self)
        assert gs.digest(before)==plan['graph_sha256']
        assert len(before)==plan['unfolded_leaves']
        for change in plan['transforms']:gs.rotate(self,change['pattern'])
        self.name_sequences()
        assert gs.graph(self)==before
        return self

def rebuild(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=False)
    b,ledger,rows=opt.compile_candidate(ReassociatedOneStack,out/'machine')
    old=opt.OneStack(opt.SOURCE);old.build_tree()
    before,after=gs.graph(old),gs.graph(b)
    assert before==after
    files=['optimize.py','grammar_search.py','grammar-plan.json','build_selected.py',
        'baseline/code/compact/source.py','baseline/code/compact/direct.py',
        'baseline/code/build.py','baseline/code/shared/backend.py',
        'baseline/code/shared/vendor/TMBuilder.py','baseline/code/shared/vendor/tm.py']
    bindings={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in files}
    certificate=dict(format='exact-unfolded-primitive-control-graph-v1',
        from_class='OneStack',to_class='ReassociatedOneStack',entry_leaf=0,
        unfolded_leaves=len(before),graphs_equal=True,graph_sha256=gs.digest(before),
        reference_graph=before,candidate_graph=after,
        semantics='Every primitive label and successor, including both DECNZ outcomes, is equal under preorder occurrence identity.',
        input_sha256=bindings,selected_table_sha256=ledger['boot']['sha256'])
    (out/'grammar-certificate.json').write_text(json.dumps(certificate,sort_keys=True,indent=2)+'\n')
    (out/'input-manifest.json').write_text(json.dumps(bindings,sort_keys=True,indent=2)+'\n')
    return b,ledger,rows

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',required=True,type=Path);a=p.parse_args()
    b,l,r=rebuild(a.out);print(json.dumps(l,indent=2))
