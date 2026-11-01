"""Emit complete third-pass polygons, literal sources and contact certificates.

No Collatz search enters the finite polygon definition. The accepted whole-plane
witness is a separate conditional construction. The final theorem and review
status are recorded in the manuscripts and frozen review bindings.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path

import geometry_v3 as G
from spine_frame_v3 import SystemV3 as ParitySystem
from scaffold_v3 import SystemV3 as FullSystem


def canonical_bytes(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':'))+'\n').encode()


def sha256(obj):
    return hashlib.sha256(canonical_bytes(obj)).hexdigest()


CANDIDATES = ('parity30-profile14', 'stream31-profile14')


def build(candidate=CANDIDATES[0]):
    if candidate not in CANDIDATES:
        raise ValueError(candidate)
    selected = candidate.startswith('parity30')
    source = ParitySystem() if selected else FullSystem()
    source.frame_checks()
    manifest = source.manifest()
    H = len({c for t in source.tiles for c in (t.east,t.west)})
    V = len({c for t in source.tiles for c in (t.north,t.south)})
    params = G.default_parameters(H,V)
    out = G.compile_tiles([t.edges for t in source.tiles],params)
    certificate = G.full_certificate(params)
    for p,t in zip(out['polygons'],source.tiles):
        p['name'] = t.name
    names = [t.name for t in source.tiles]
    root_tile = source.by_name['ROOT']
    root = (G.northeast_contact(out,root_tile.east,root_tile.north)
            if selected else G.east_contact(out,root_tile.east))
    event_color = source.by_name['spine:RESET'].east if selected else source.event_color
    event = G.east_contact(out,event_color)
    assert root['matching_shape_indices'] == [names.index('ROOT')]
    column = 0 if selected else 1
    offset = [event['anchor'][0]-root['anchor'][0]+column*params.L,
              event['anchor'][1]-root['anchor'][1]]
    out.update(candidate=candidate, parameters=asdict(params),
               source_manifest_sha256=source.digest(),
               arithmetic_manifest_sha256=manifest.get('transducer_manifest_sha256'),
               ordinary_tileability='unconditional: background and quiet rooted whole-plane tilings',
               acceptance_track='B: existence of a completed tiling with grounded recurrence',
               stream_scope='accepted rooted rows have finite support; nonstandard rooted rows cannot precede a later reset',
               observer={'root':root,'event':event,'root_index':names.index('ROOT'),
                         'event_column_offset':column,'event_anchor_offset':offset,
                         'macro_pitch':params.L,
                         'event_context':'ROOT spine column' if selected else 'first digit column of ROOT',
                         'global_formula':'exists p,u,v: root(p,u,v) and forall k>=1 exists integer j>=k: event(p+dx*u+(dy+j*L)*v,u,v)',
                         'event_source_indices_in_context':[names.index('spine:RESET')] if selected else list(source.event_first_indices)},
               contact_certificate_sha256=sha256(certificate))
    return out,source,certificate


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate',choices=CANDIDATES,default=CANDIDATES[0])
    parser.add_argument('--all',action='store_true')
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    summary=[]
    for name in CANDIDATES if args.all else (args.candidate,):
        out,source,cert=build(name)
        for suffix,obj in (('',out),('-source',source.manifest()),('-contact-certificate',cert)):
            (args.out/(name+suffix+'.json')).write_bytes(canonical_bytes(obj))
        item={'candidate':name,'polygon_sha256':sha256(out),
              'file_bytes':len(canonical_bytes(out)),'source_sha256':source.digest(),
              'certificate_sha256':sha256(cert),'summary':out['summary'],'observer':out['observer']}
        summary.append(item)
        print(json.dumps({k:v for k,v in item.items() if k!='observer'},sort_keys=True),flush=True)
    (args.out/'summary-v3.json').write_bytes(canonical_bytes(summary))


if __name__=='__main__':
    main()
