"""Frozen complete control-region experiments; replay performs no search."""
from pathlib import Path
import argparse
import importlib.util
import json

HERE=Path(__file__).resolve().parent
COMPACT=HERE.parent


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value)
    return value


producer=module('control_regions_fixed_measure',HERE/'measure.py')
neutral=module('control_regions_fixed_neutral',HERE/'measure_neutral.py')
selector=module('control_regions_fixed_select',HERE/'select.py')


def build(case,out):
    recipes=json.loads((HERE/'recipes.json').read_text())
    recipe=recipes[case];folder=HERE/'plans'/case;out=Path(out)
    inputs=dict(plan=json.loads((folder/'grammar.json').read_text()),
        groups=json.loads((folder/'groups.json').read_text()),**recipe['options'])
    result=neutral.build(out,**inputs) if recipe.get('producer')=='neutral' else producer.build(COMPACT/recipe['source'],out,**inputs)
    assert [result[k] for k in ('raw_states','states','event_states')]==recipe['counts']
    assert result['event_table_sha256']==recipe['events_sha256']
    producer.compiler.base.dump(out/'fixed-recipe.json',dict(case=case,recipe=recipe,
        grammar_sha256=producer.compiler.base.sha(folder/'grammar.json'),
        groups_sha256=producer.compiler.base.sha(folder/'groups.json'),
        recipes_sha256=producer.compiler.base.sha(HERE/'recipes.json'),
        generator_sha256=producer.compiler.base.sha(Path(__file__)),optimization_search=False))
    if 'selected' in recipe:
        selected=selector.select(COMPACT/recipe['source'],out,out.parent/(out.name+'_selected'),folder/'completion.json')
        assert [selected[k] for k in ('raw_states','states','event_states')]==recipe['selected']['counts']
        assert selected['event_table_sha256']==recipe['selected']['events_sha256']
    return result


def compare(a,b):
    files=lambda p:{q.relative_to(p).as_posix():q for q in p.rglob('*') if q.is_file()}
    left,right=files(a),files(b)
    assert left.keys()==right.keys(),(str(a),'file inventory')
    for key in left:assert left[key].read_bytes()==right[key].read_bytes(),(str(a),key)
    return len(left)


if __name__=='__main__':
    recipes=json.loads((HERE/'recipes.json').read_text())
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--case',choices=recipes)
    p.add_argument('--reproduce',action='store_true');a=p.parse_args()
    if a.reproduce:
        assert not a.out.exists();a.out.mkdir(parents=True);counts={}
        for case in [a.case] if a.case else recipes:
            build(case,a.out/case);counts[case]=compare(a.out/case,HERE/'machines'/case)
            if 'selected' in recipes[case]:
                counts[case+'_selected']=compare(a.out/(case+'_selected'),HERE/'machines'/(case+'_selected'))
        print(json.dumps(dict(fixed_plan=True,optimization_search=False,canonical_artifacts=counts),indent=2))
    else:
        assert a.case is not None;r=build(a.case,a.out)
        print(json.dumps({k:r[k] for k in ('raw_states','states','event_states','registers')},indent=2))
