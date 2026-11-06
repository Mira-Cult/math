"""Remove certified zero tests and the finite empty control they expose.

This optional grammar pass is admitted only at the all-zero source entry.
It preserves the ordered event/register computation, not physical event times.
The supplied invariant and local rewrite record are replayed separately.
"""
from pathlib import Path
from copy import copy
from functools import lru_cache
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[2]
sys.path[:0]=[str(ROOT/'shared'),str(ROOT/'compression/grammar')]
from build_baseline import grammar
from contextual_quotient import analyze
from TMBuilder import Sequence

DOMAIN='all-zero source entry, after the separately verified blank bootstrap'
EVENT_SCOPE='ordered events and retained register operations preserved; primitive and physical times may change'


def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def install(builder,nodes,root):
    builder.sequences=[Sequence(tuple(pair)) for pair in nodes]
    builder.sequence_lookup={tuple(pair):i for i,pair in enumerate(nodes)}
    for i,sequence in enumerate(builder.sequences):
        sequence.name='main().0' if i==root else f'contextual_tree_{i}.0'


def unpack(data):
    return [tuple(child['node'] if 'node' in child else child['op'] for child in pair)
            for pair in data['nodes']]


def pack(child):
    return {'node':child} if type(child) is int else {'op':child}


def apply(builder):
    """Mutate only the finished binary grammar; return a replayable certificate."""
    before=grammar(builder)
    original=tuple(unpack(before));root=before['root']
    old=copy(builder);install(old,original,root)
    summary,replacements,live,abstract=analyze(old)
    nodes=[];lookup={};images={};rewrites={}

    def pair_node(left,right):
        pair=(left,right)
        if pair not in lookup:
            lookup[pair]=len(nodes);nodes.append(pair)
        return lookup[pair]

    @lru_cache(None)
    def demand(value):
        absent=-10**9
        if type(value) is str:
            if value.startswith('_break.'):return int(value.split('.')[1]),absent
            if value.startswith('_continue.'):return absent,int(value.split('.')[1])
            if value.endswith('.decnz'):return 1,absent
            if value=='beep' or value.endswith('.inc'):return 0,absent
            raise ValueError('unknown primitive')
        left,right=nodes[value];a,b=demand(left),demand(right)
        return max(a[0]-1,b[0]),max(a[1],b[1]-1)

    def emit(value):
        if type(value) is str:return value
        if value in images:return images[value]
        left,right=(emit(replacements.get((value,bit),child))
                    for bit,child in enumerate(original[value]))
        rule='pair'
        if (type(left) is str and left.startswith('_break.')
                and int(left.split('.')[1])>=1 and (value,1) not in live):
            result='_break.'+str(int(left.split('.')[1])-1);rule='escape'
        elif left=='_break.0' and max(demand(right))<=0:
            result=right;rule='drop-left-identity'
        elif right=='_break.0' and max(demand(left))<=0:
            result=left;rule='drop-right-identity'
        else:result=pair_node(left,right)
        # The physical dispatcher has a binary root contract. Keep the final
        # root pair when a tiny fixture would otherwise reduce to one leaf.
        if value==root and type(result) is not int:
            result=pair_node(left,right);rule='pair'
        images[value]=result;rewrites[value]=rule
        return result

    target_root=emit(root)
    if type(target_root) is not int:
        raise ValueError('this adapter requires a nontrivial binary target root')
    install(builder,nodes,target_root)
    certificate=dict(schema='horn-contextual-tree-v1',domain=DOMAIN,event_scope=EVENT_SCOPE,
        input_grammar=before,input_grammar_sha256=digest(before),
        output_grammar_sha256=digest(grammar(builder)),
        states_at_occurrences=[None if state is None else ''.join(map(str,state))
                              for state in abstract['states']],
        zero_rows=[list(key) for key in sorted(replacements)],
        target_nodes=[[pack(child) for child in pair] for pair in nodes],
        target_root=target_root,
        node_images=[pack(images[i]) for i in range(len(original))],
        rewrite_rules=[rewrites[i] for i in range(len(original))],
        measurements={**summary,'old_nodes':len(original),
            'new_nodes':len(list(builder.reachable())),
            'nontrivial_rewrites':sum(rule!='pair' for rule in rewrites.values())})
    from check_contextual_tree import check
    certificate['replay']=check(old,builder,certificate)
    builder.contextual_tree_certificate=certificate
    return certificate


class ContextualTreeMixin:
    def __init__(self,*args,contextual_tree=True,**kwargs):
        if type(contextual_tree) is not bool:raise TypeError('contextual_tree must be bool')
        super().__init__(*args,**kwargs)
        self.contextual_tree=contextual_tree
        self.contextual_tree_certificate=None

    def build_tree(self):
        super().build_tree()
        if self.contextual_tree:apply(self)
        return self
