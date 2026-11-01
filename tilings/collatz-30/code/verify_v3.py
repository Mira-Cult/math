"""Rebuild and verify selected literal polygons, observer and exact proof cases."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

from build_v3 import build, canonical_bytes, sha256
from test_geometry_v3 import verify_certificate, simple_orthogonal, periodic_core_check
from geometry_v3 import Parameters


def main():
    root = Path(__file__).resolve().parents[1]
    pins = json.loads((root/'inputs/selection-v3.json').read_text())
    out, source, certificate = build(pins['candidate'])
    literal = json.loads((root/'inputs/parity30-wang.json').read_text())
    assert canonical_bytes(literal) == canonical_bytes(source.manifest())
    assert source.digest() == pins['source_sha256']
    assert sha256(out) == pins['polygon_sha256']
    assert len(canonical_bytes(out)) == pins['file_bytes']
    assert sha256(certificate) == pins['certificate_sha256']
    assert verify_certificate(json.loads(canonical_bytes(certificate)))
    periodic_core_check(Parameters(**out['parameters']))
    for p in out['polygons']:
        simple_orthogonal(p['vertices'])
        assert len(p['vertices']) == p['sides'] == 14
    assert Counter(p['sides'] for p in out['polygons']) == {14: 30}
    assert json.loads(canonical_bytes(out['summary'])) == pins['summary']
    assert json.loads(canonical_bytes(out['observer'])) == pins['observer']
    observer = (root/'inputs/observer-v3.txt').read_bytes()
    assert len(observer) == pins['observer_spec_bytes']
    assert hashlib.sha256(observer).hexdigest() == pins['observer_sha256']
    for name, lengths, indices in [('root',(38,43),[29]),('event',(32,13),[6,27])]:
        marker = out['observer'][name]
        assert tuple(marker['lengths']) == lengths
        assert marker['matching_shape_indices'] == indices
    assert out['observer']['event_anchor_offset'] == [13,-34]
    assert out['observer']['macro_pitch'] == 66
    assert [i for i,t in enumerate(source.tiles)
            if t.name.startswith('spine:') and t.east == source.event_color] == [27]
    text = (root/'manuscripts/polygon-v3-theorem.md').read_text()
    table = [tuple(map(int, m)) for m in re.findall(
        r'^\| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \|$', text, re.M)]
    assert table == [(p['index'],*p['profiles']) for p in out['polygons']]
    print(json.dumps({'candidate':pins['candidate'],'shapes':30,'genuine_sides':420,
                      'max_sides':14,'coordinate_bound':79,
                      'polygon_sha256':pins['polygon_sha256'],
                      'contact_certificate_sha256':pins['certificate_sha256'],
                      'observer_bytes':len(observer),
                      'finite_certificate_summary':out['certificate_summary'],
                      'scope':'exact finite obligations; infinite equivalence is the separate ordinary proof'},sort_keys=True))


if __name__ == '__main__':
    main()
