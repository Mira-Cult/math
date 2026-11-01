"""Additional nonauthor audit of literal endpoint14 contact witnesses.

Author: task agent /root/arithmetic.  This checks geometric witnesses only;
it is not an independent review of that agent's arithmetic manuscripts.
The producer uses rectangle decomposition and a compressed-grid flood fill.
The author's certificate checker uses a rectangle-transfer membership formula.
This audit instead ray-crosses the literal core/envelope outlines, then checks
every overlap cell and every closed edge of every cavity's external boundary.
All coordinates are integers: these are exact cell decompositions, not sampled
floating-point pictures.  The arbitrary-placement and infinite-plane argument
remains an ordinary mathematical proof, not a consequence of bounded testing.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

import geometry_v3 as G
from test_geometry_v3 import verify_certificate


def outline_cells(vertices):
    """Exact horizontal-ray parity at doubled unit-cell centres."""
    edges = list(zip(vertices, vertices[1:] + vertices[:1]))
    assert all((a[0] == b[0]) != (a[1] == b[1]) for a, b in edges)
    result = set()
    for x in range(min(p[0] for p in vertices), max(p[0] for p in vertices)):
        for y in range(min(p[1] for p in vertices), max(p[1] for p in vertices)):
            crossings = sum(
                a[0] == b[0] and 2*a[0] > 2*x+1
                and min(2*a[1], 2*b[1]) < 2*y+1 < max(2*a[1], 2*b[1])
                for a, b in edges)
            if crossings % 2:
                result.add((x, y))
    return result


def local_cell(cell, pose):
    turns, (a, b) = pose
    x, y = 2*cell[0]+1-2*a, 2*cell[1]+1-2*b
    x, y = ((x, y), (-y, x), (-x, -y), (y, -x))[-turns % 4]
    assert x % 2 == y % 2 == 1
    return x // 2, y // 2


def cells_in_rectangle(rectangle):
    x0, y0, x1, y1 = rectangle
    assert all(type(x) is int for x in rectangle) and x0 < x1 and y0 < y1
    return {(x, y) for x in range(x0, x1) for y in range(y0, y1)}


def inside_one(cell, poses, core):
    return any(local_cell(cell, p) in core for p in poses)


def verify_witness(witness, core, envelope, counts):
    if witness['kind'] == 'overlap':
        a, b = witness['a'], witness['b']
        assert a != b
        cells = cells_in_rectangle(witness['overlap'])
        for cell in cells:
            assert local_cell(cell, a) in core and local_cell(cell, b) in core
        counts['overlap_rectangles'] += 1
        counts['overlap_cells_in_each_core'] += len(cells)
        return

    assert witness['kind'] == 'cavity'
    poses = witness['poses']
    region = set()
    for rectangle in witness['component']:
        cells = cells_in_rectangle(rectangle)
        assert not region & cells
        region.update(cells)
    assert 0 < len(region) == witness['area'] < len(core)
    assert all(not inside_one(cell, poses, core) for cell in region)

    # Cancel internal edges of this finite union of closed unit squares.
    # Every remaining edge must border a core-filled outside cell.  A core is
    # closed, so its whole cell closure contains the edge and both endpoints.
    # Hence no open connected tile interior can leave this finite region,
    # including through a diagonal meeting or a zero-width contact.
    edges = Counter()
    for x, y in region:
        edges[((x, y), (x+1, y))] += 1
        edges[((x, y+1), (x+1, y+1))] += 1
        edges[((x, y), (x, y+1))] += 1
        edges[((x+1, y), (x+1, y+1))] += 1
    for ((x0, y0), (x1, y1)), multiplicity in edges.items():
        assert multiplicity in (1, 2)
        if multiplicity == 2:
            continue
        adjacent = ((x0, y0-1), (x0, y0)) if y0 == y1 else ((x0-1, y0), (x0, y0))
        outside = [cell for cell in adjacent if cell not in region]
        assert len(outside) == 1 and inside_one(outside[0], poses, core)
        counts['cavity_closed_boundary_edges'] += 1

    missing = cells_in_rectangle(witness['unfilled'])
    assert missing <= region
    assert all(not inside_one(cell, poses, envelope) for cell in missing)
    counts['cavities'] += 1
    counts['cavity_cells'] += len(region)
    counts['uncovered_cells'] += len(missing)


def verify_cells(certificate):
    # The separate checker proves exact candidate/pair universe coverage,
    # structural hypotheses, allowed pose bindings and prerequisite order.
    # None of its membership, rectangle or flood-fill helpers is called below.
    assert verify_certificate(certificate)
    P = G.Parameters(**certificate['parameters'])
    core = outline_cells(G.polygon(P, P.V-1, 0, 0, P.H-1))
    envelope = outline_cells(G.polygon(P, 0, P.H-1, P.V-1, 0))
    base = outline_cells(G.polygon(P, 0, 0, 0, 0))
    area = P.L**2 - P.south_depth*(P.V-1) - P.east_depth*(P.H-1)
    assert core <= base <= envelope and len(core) == area
    assert len(envelope) == 2*P.L**2-area
    assert len(base) == len({(x % P.L, y % P.L) for x, y in base}) == P.L**2
    bands = {(x, y) for x in range(P.horizontal_length, P.horizontal_length+P.V-1)
             for y in range(P.L-P.south_depth, P.L)} | {
             (x, y) for x in range(P.east_depth)
             for y in range(P.vertical_length, P.vertical_length+P.H-1)}
    assert base-core == bands

    corners = [certificate['west']['first'], *certificate['west']['seconds'],
               *certificate['north'], *certificate['east'], *certificate['south']]
    pairs = [*certificate['west']['pairs'], *certificate['east_south']]
    counts = Counter()
    for record in corners + pairs:
        for rejection in record['rejections']:
            verify_witness(rejection['witness'], core, envelope, counts)
    summary = G.certificate_summary(certificate)
    assert counts['overlap_rectangles'] == summary['rejection_kinds']['overlap']
    assert counts['cavities'] == summary['rejection_kinds']['cavity']
    encoded = (json.dumps(certificate, sort_keys=True, separators=(',', ':'))+'\n').encode()
    return {
        'parameters': certificate['parameters'],
        'certificate_sha256': hashlib.sha256(encoded).hexdigest(),
        'core_area': len(core), 'envelope_area': len(envelope),
        'base_area_and_distinct_residues': len(base),
        'open_band_areas': sorted([P.south_depth*(P.V-1), P.east_depth*(P.H-1)]),
        'single_corner_cases': len(corners), 'joint_pair_cases': len(pairs),
        'independent_ray_crossing_audit': dict(sorted(counts.items())),
        'scope': 'finite witness audit; global converse remains an ordinary proof',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--h', type=int, default=8)
    parser.add_argument('--v', type=int, default=6)
    args = parser.parse_args()
    certificate = (json.loads(args.certificate.read_text()) if args.certificate
                   else G.full_certificate(G.default_parameters(args.h, args.v)))
    print(json.dumps(verify_cells(certificate), sort_keys=True))


if __name__ == '__main__':
    main()
