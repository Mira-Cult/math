"""Explicit opt-in complete build for contextual tree reduction.

The existing integrated recipe and its defaults stay unchanged. An optional
exact list of intrinsic sites permits measured composition with source-neutral
intrinsic selection. The temporary constructor adapter is restored on exit.
"""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path[:0]=[str(HERE),str(ROOT/'compression'),str(ROOT/'compression/native'),
             str(ROOT/'compression/grammar'),str(ROOT/'compression/source')]
from contextual_tree import ContextualTreeMixin
from countdown import CountdownHornerBuilder
import integrated_build,fused_horner
import intrinsic_build


class ContextualTreeBuilder(ContextualTreeMixin,CountdownHornerBuilder):
    pass


class SelectedContextualTreeBuilder(ContextualTreeMixin,intrinsic_build.SelectedIntrinsicBuilder):
    pass


def constructor(*,intrinsic_sites=None,enabled=True,selected=False,refactor_options=None,instances=None):
    """Return the explicit constructor used by the complete build/audit recipe."""
    if selected and intrinsic_sites is not None:
        raise ValueError('selected recipe owns and checks the complete intrinsic site set')
    def make(*args,**kwargs):
        if intrinsic_sites is not None:kwargs['intrinsic_sites']=intrinsic_sites
        if refactor_options is not None:kwargs['refactor_options']=refactor_options
        cls=SelectedContextualTreeBuilder if selected else ContextualTreeBuilder
        result=cls(*args,contextual_tree=enabled,**kwargs)
        if instances is not None:instances.append(result)
        return result
    return make


def build(source,out,*,intrinsic_sites=None,enabled=True,selected=False,refactor_options=None):
    instances=[]
    make=constructor(intrinsic_sites=intrinsic_sites,enabled=enabled,selected=selected,
                     refactor_options=refactor_options,instances=instances)
    if selected:
        original=intrinsic_build.SelectedIntrinsicBuilder
        try:
            intrinsic_build.SelectedIntrinsicBuilder=make
            metadata=intrinsic_build.build(source,out)
        finally:intrinsic_build.SelectedIntrinsicBuilder=original
    else:
        original=fused_horner.HornerBuilder
        try:
            fused_horner.HornerBuilder=make
            metadata=integrated_build.build(source,out,horner=True)
        finally:fused_horner.HornerBuilder=original
    if len(instances)!=1:raise AssertionError('constructor invocation count')
    b=instances[0]
    metadata['countdown_loops']=True
    metadata['countdown_fusion']=b.countdown_certificate
    metadata['contextual_tree_enabled']=enabled
    metadata['checked_selected_intrinsic_recipe']=selected
    metadata['explicit_intrinsic_sites']=list(intrinsic_sites) if intrinsic_sites is not None else None
    metadata['explicit_refactor_options']=refactor_options
    metadata['contextual_tree_recipe_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    metadata['contextual_tree_producer_sha256']=hashlib.sha256((HERE/'contextual_tree.py').read_bytes()).hexdigest()
    metadata['review']='producer generation; invariant/structural replay; independent review and literal audits separate'
    if enabled:
        certificate=b.contextual_tree_certificate
        metadata['contextual_tree_replay']=certificate['replay']
        metadata['equivalence']='source theorem plus zero-entry tree invariant/structural replay, runtime proof and contextual quotient; event timing changes'
        (Path(out)/'contextual-tree-certificate.json').write_text(json.dumps(certificate,sort_keys=True,indent=2)+'\n')
    (Path(out)/'metadata.json').write_text(json.dumps(metadata,sort_keys=True,indent=2)+'\n')
    return metadata


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--source',type=Path,default=ROOT/'compression/source/source_head_stream.py')
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--intrinsic-sites',type=Path,help='JSON array of exact AST site strings')
    parser.add_argument('--disable-tree',action='store_true')
    parser.add_argument('--selected',action='store_true',help='compose the pinned four-site source recipe and its actual-lowering checks')
    args=parser.parse_args()
    sites=json.loads(args.intrinsic_sites.read_text()) if args.intrinsic_sites else None
    result=build(args.source,args.out,intrinsic_sites=sites,enabled=not args.disable_tree,selected=args.selected)
    print(json.dumps({key:result[key] for key in ('states','raw_states','exact_states','table_sha256','profile')},indent=2))
