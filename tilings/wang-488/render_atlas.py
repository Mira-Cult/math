#!/usr/bin/env python3
"""Render the exact 488 oriented Wang tiles as a labeled inventory, not a tiling.

Requires Python 3 and Inkscape for PNG export. No third-party Python packages.
Run: python render_atlas.py [--svg-only]
Input bytes are checked against the independently reviewed artifact hash.
"""
from __future__ import annotations

import argparse
import colorsys
import csv
import hashlib
import html
import json
import subprocess
from pathlib import Path
from xml.etree import ElementTree as ET

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'k215_diagonal_488.tsv'
EXPECTED_SHA256 = '371ebc4063c47ba3491d99c6884faa43633d3ea2600411d9eee9b4a020207017'
SOURCE_COMMIT = 'cebfe3e282ee65337d9fa69c274d5321d757e340'
SOURCE_URL = 'https://github.com/Mira-Cult/math/blob/main/tilings/wang-488/k215_diagonal_488.tsv'
W, H = 3600, 4500
BG = '#101923'
FG = '#f4f2e9'
MUTED = '#a8b6c6'
GOLD = '#ffce6c'
SANS = 'DejaVu Sans'
MONO = 'DejaVu Sans Mono'
SPECIAL = {
    'sym:0': ('0', '#264158', '#ffffff'),
    'sym:1': ('1', '#e4f5f1', '#152a35'),
    'bottom': ('B', '#df637f', '#13232c'),
    'init:R': ('R', '#ffb25b', '#13232c'),
    'wall': ('W', '#78b9f3', '#13232c'),
    'wall:start': ('WS', '#aa8ce8', '#13232c'),
}


def palette(color: str) -> tuple[str, str, str]:
    if color in SPECIAL:
        return SPECIAL[color]
    assert color.startswith('head:')
    q = int(color[5:])
    # A deterministic bijective display palette, not a claim that 215 hues
    # can be visually discriminated. The printed Hn edge code is authoritative.
    hue = (q * 0.6180339887498949 + 0.07) % 1.0
    saturation = [0.64, 0.73, 0.82][q % 3]
    lightness = [0.65, 0.72, 0.79][(q // 3) % 3]
    r, g, b = colorsys.hls_to_rgb(hue, lightness, saturation)
    rgb = '#%02x%02x%02x' % tuple(round(v * 255) for v in (r, g, b))
    channels = [v / 12.92 if v <= 0.04045 else ((v + 0.055) / 1.055) ** 2.4 for v in (r, g, b)]
    luminance = sum(v * w for v, w in zip(channels, (0.2126, 0.7152, 0.0722)))
    ink = '#000000' if (luminance + 0.05) / 0.05 >= 1.05 / (luminance + 0.05) else '#ffffff'
    return f'H{q}', rgb, ink


def main() -> None:
    args = argparse.ArgumentParser()
    args.add_argument('--svg-only', action='store_true')
    ns = args.parse_args()
    raw = SOURCE.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == EXPECTED_SHA256, (digest, EXPECTED_SHA256)
    rows = list(csv.DictReader(raw.decode().splitlines(), delimiter='\t'))
    dirs = ('north', 'east', 'south', 'west')
    assert len(rows) == 488
    assert [int(t['index']) for t in rows] == list(range(488))
    assert len({tuple(t[d] for d in dirs) for t in rows}) == 488
    assert [int(t['index']) for t in rows if t['seed'] == '1'] == [487]
    assert tuple(rows[487][d] for d in dirs) == ('wall:start', 'init:R', 'bottom', 'sym:0')
    colors = sorted({t[d] for t in rows for d in dirs})
    assert len(colors) == 221
    assert len({palette(c)[0] for c in colors}) == 221
    assert len({palette(c)[1] for c in colors}) == 221

    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
    parts += ['<title>488 Wang tiles: exact seeded-half-plane tile inventory</title>',
              '<desc>All 488 distinct oriented Wang tile types from the pinned K215 diagonal construction, each shown once. Four triangular faces encode the north, east, south and west edge colors. Edge codes disambiguate every color. Seed tile 487 is enlarged and outlined in gold. The catalog is not a tiling; this is not an unrestricted whole-plane result.</desc>',
              f'<metadata>{html.escape(json.dumps({"input_sha256": digest, "source_commit": SOURCE_COMMIT, "source_url": SOURCE_URL, "tile_count":488,"edge_color_count":221,"seed_index":487,"tile_order":"north,east,south,west","display":"inventory, not a tiling","palette_rule":"Exact textual edge codes, deterministic auxiliary colors"}))}</metadata>',
              '<defs><linearGradient id="background" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#182735"/><stop offset="1" stop-color="#0b121c"/></linearGradient></defs>',
              f'<rect width="{W}" height="{H}" fill="url(#background)"/>']

    def rect(x, y, w, h, fill, rx=0, stroke=None, sw=1):
        parts.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{rx}" fill="{fill}"' + (f' stroke="{stroke}" stroke-width="{sw}"' if stroke else '') + '/>')

    def text(x, y, value, size=36, fill=FG, weight='400', anchor='start', family=SANS, extra=''):
        parts.append(f'<text x="{x}" y="{y}" font-family="{family}" font-size="{size}" font-weight="{weight}" fill="{fill}" text-anchor="{anchor}" xml:space="preserve" {extra}>{html.escape(str(value))}</text>')

    def tile(t, x, y, s=130, enlarged=False):
        i = int(t['index'])
        attrs = ' '.join(f'data-{d}="{html.escape(t[d])}"' for d in dirs)
        parts.append(f'<g id="tile-{i}" data-index="{i}" data-seed="{t["seed"]}" {attrs} transform="translate({x},{y})">')
        parts.append(f'<title>Tile {i}: N={t["north"]}; E={t["east"]}; S={t["south"]}; W={t["west"]}' + ('; distinguished seed' if i == 487 else '') + '</title>')
        if i == 487:
            rect(-8, -8, s+16, s+16, '#9a6b22', 9)
            rect(-4, -4, s+8, s+8, GOLD, 5)
        c = s/2
        pts = [f'0,0 {s},0 {c},{c}', f'{s},0 {s},{s} {c},{c}', f'{s},{s} 0,{s} {c},{c}', f'0,{s} 0,0 {c},{c}']
        for d, p in zip(dirs, pts):
            code, fill, ink = palette(t[d])
            parts.append(f'<polygon data-edge="{d}" data-color="{t[d]}" points="{p}" fill="{fill}" stroke="{BG}" stroke-width="0.8"/>')
        rect(0, 0, s, s, 'none', 0, '#526575', 0.9)
        f = 16 if not enlarged else 29
        # Labels are centered on each edge-facing triangle, not rotated.
        positions = [(c,s*.146+f*.35),(s*.82,c+f*.35),(c,s*.854+f*.35),(s*.18,c+f*.35)]
        for d, (tx,ty) in zip(dirs, positions):
            code, fill, ink = palette(t[d])
            text(tx,ty,code,f,ink,'700','middle',MONO)
        r = s*.151
        parts.append(f'<circle cx="{c}" cy="{c}" r="{r}" fill="{BG}" stroke="' + (GOLD if i==487 else '#638092') + '" stroke-width="1.1"/>')
        text(c,c+(17 if not enlarged else 32)*.35,i,17 if not enlarged else 32,GOLD if i==487 else FG,'700','middle',MONO)
        parts.append('</g>')

    # Editorial masthead. The qualifiers are intentionally visible at feed size.
    rect(104, 86, 10, 51, GOLD, 5)
    text(140, 126, 'FINITE RULES  /  INFINITE COMPUTATION', 36, MUTED, '700', extra='letter-spacing="4"')
    text(102, 355, '488 Wang tiles', 222, FG, '700', extra='letter-spacing="-7"')
    rect(2670, 187, 828, 177, '#243847', 24, '#4c6573', 2)
    text(3084, 300, '975 → 488', 102, GOLD, '700', 'middle')
    text(110, 458, 'Seeded half-plane encoding of ZFC consistency', 61, '#d7e4e9', '400', extra='letter-spacing="-1"')
    text(110, 554, '488 distinct tiles', 43, FG, '700')
    text(680, 554, '221 edge colors', 43, FG, '700')
    text(1227, 554, 'K215', 43, FG, '700')
    text(1440, 554, 'One distinguished seed', 43, FG, '700')
    text(110, 632, 'All tiles shown once. Fixed orientation. Match equal edge codes.', 38, MUTED)

    # 20 complete rows of 24 tiles, followed by seven ordinary tiles and an
    # enlarged seed in the last row. Every data-index occurs exactly once.
    for t in rows[:487]:
        i = int(t['index'])
        tile(t, 102 + (i % 24) * 142, 704 + (i // 24) * 142)
    tile(rows[487], 1250, 3544, 266, True)
    text(1620, 3577, 'THE SEED', 33, GOLD, '700', extra='letter-spacing="3"')
    text(1620, 3643, 'Tile 487', 58, FG, '700')
    text(1620, 3700, 'N = wall:start   •   E = init:R', 34, '#c4d2de', family=MONO)
    text(1620, 3751, 'S = bottom       •   W = sym:0', 34, '#c4d2de', family=MONO)
    text(102, 3744, 'Read left to right, top to bottom.', 31, MUTED)
    text(102, 3794, 'Center numbers are the original tile indices.', 31, MUTED)

    # Dense details live below the artwork; scope stays unmistakable.
    rect(102, 3890, 3396, 418, '#1d2c3a', 26, '#3f5361', 2)
    text(169, 3994, 'Tile inventory, not a tiling', 77, FG, '700')
    text(169, 4077, 'Not an unrestricted whole-plane result', 56, GOLD, '700')
    text(172, 4158, 'Edge key:', 36, FG, '700')
    text(385, 4158, 'Hn = head:n   •   0 = sym:0   •   1 = sym:1', 35, '#c4d2de', family=MONO)
    text(172, 4226, 'B = bottom   •   R = init:R   •   W = wall   •   WS = wall:start', 35, '#c4d2de', family=MONO)
    text(102, 4377, 'K215 diagonal construction • 480 instruction + 4 background + 4 boundary / seed tiles', 32, MUTED)
    text(102, 4435, 'Exact TSV SHA-256: 371ebc4063c47ba3491d99c6884faa43633d3ea2600411d9eee9b4a020207017', 25, '#8c9eb1', family=MONO)
    parts.append('</svg>')
    svg = '\n'.join(parts) + '\n'
    tree = ET.fromstring(svg)
    groups = [e for e in tree.iter() if e.attrib.get('data-index') is not None]
    assert [int(e.attrib['data-index']) for e in groups] == list(range(488))
    for group, t in zip(groups, rows):
        assert all(group.attrib['data-'+d] == t[d] for d in dirs)
        polys = [e for e in group if e.tag.endswith('polygon')]
        assert [(p.attrib['data-edge'], p.attrib['data-color']) for p in polys] == [(d,t[d]) for d in dirs]
        assert [p.attrib['fill'] for p in polys] == [palette(t[d])[1] for d in dirs]
    svg_path = ROOT / '488-wang-tiles.svg'
    svg_path.write_text(svg)
    palette_data = [{'source_color': c, 'edge_code':palette(c)[0], 'hex_color':palette(c)[1], 'label_ink':palette(c)[2]} for c in colors]
    (ROOT / 'palette.json').write_text(json.dumps(palette_data, indent=2) + '\n')
    report = {'source_commit': SOURCE_COMMIT,'source_url':SOURCE_URL,'source_sha256':digest,'tile_count':len(rows),'distinct_tile_count':len({tuple(t[d] for d in dirs) for t in rows}),'edge_color_count':len(colors),'unique_palette_colors':len({palette(c)[1] for c in colors}),'unique_display_codes':len({palette(c)[0] for c in colors}),'seed_index':487,'svg_tile_group_count':len(groups),'svg_contains_all_tiles_exactly_once':True,'svg_edges_verified_against_tsv':True,'dimensions':[W,H]}
    (ROOT / 'atlas-verification.json').write_text(json.dumps(report, indent=2) + '\n')
    if not ns.svg_only:
        subprocess.run(['inkscape',str(svg_path),'--export-type=png','--export-filename='+str(ROOT/'488-wang-tiles.png'),'--export-width='+str(W),'--export-height='+str(H)],check=True)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
