"""Replay the selected 266-state construction from frozen plans, without search."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import tempfile

ROOT=Path(__file__).resolve().parent.parent
SOURCE=ROOT/'reproducibility/source'
CASE='reuse_clock_roles_zero_geometry'
HERE=SOURCE/'problems/np-conp-formulations/selector/continuation/compact/control_regions'

def verify_sources():
    manifest=json.loads((ROOT/'SOURCE_MANIFEST.json').read_text())
    for entry in manifest['files']:
        path=ROOT/entry['path']
        if hashlib.sha256(path.read_bytes()).hexdigest()!=entry['sha256']:
            raise ValueError('Exported input hash mismatch: '+entry['path'])
    return manifest

def reproduce(out):
    manifest=verify_sources()
    if out.exists():raise ValueError('Output directory must not already exist')
    out.mkdir(parents=True)
    spec=importlib.util.spec_from_file_location('selected_fixed_reproduction',HERE/'fixed.py')
    fixed=importlib.util.module_from_spec(spec);spec.loader.exec_module(fixed)
    fixed.build(CASE,out/CASE)
    count=sum(fixed.compare(out/name,HERE/'machines'/name) for name in (CASE,CASE+'_selected'))
    assert count==54
    hashes={name:hashlib.sha256((out/(CASE+'_selected')/name).read_bytes()).hexdigest() for name in ('events.tm','machine.tm')}
    assert hashes['events.tm']=='c5b0a16ce6edba5df3372ab9d6290db8d7ca747a6660a9d10f3a9d1fc8e5331c'
    assert hashes['machine.tm']=='668c5c91d2510aadc0fac6342f80fc3f4d248d6a2fd828d375a45b57e780e712'
    return {'format':'np-conp-266-public-selected-reproduction-v1','case':CASE,'optimization_search':False,
            'exported_source_files_verified':len(manifest['files']),
            'source_manifest_sha256':hashlib.sha256((ROOT/'SOURCE_MANIFEST.json').read_bytes()).hexdigest(),
            'wrapper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'canonical_artifacts_byte_identical':count,
            'table_sha256':hashes,'original_all_experiment_replay':False}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path);p.add_argument('--receipt',type=Path);a=p.parse_args()
    if a.out:result=reproduce(a.out)
    else:
        with tempfile.TemporaryDirectory(prefix='npconp266-') as tmp:result=reproduce(Path(tmp)/'build')
    if a.receipt:a.receipt.parent.mkdir(parents=True,exist_ok=True);a.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
