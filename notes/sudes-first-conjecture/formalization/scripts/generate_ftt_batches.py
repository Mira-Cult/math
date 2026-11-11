#!/usr/bin/env python3
"""Generate kernel-checkable Lean proofs from the frozen FTT Lucas graph.

The generated numerals are untrusted input: every prime proof uses a checked
Lucas node and earlier proved prime lemmas. Row validity does not establish
that the row's X or T are the actual prime-pool maximum and sum.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / 'problems/prime-line-sums/inputs/cutoff2_finite_target_table_data.json'
OUT = ROOT / 'formalizations/sude/Sude/GeneratedFTT'
SHA256 = 'c270ec76ac4e1a00c1992fd78a3654695bd1ff94c940af773eff6687152772d8'
ROWS_PER_BATCH = 25
MAX_NODES_PER_MODULE = 300


def main():
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SHA256:
        raise ValueError('FTT source does not match its frozen SHA-256')
    data = json.loads(raw)
    rows = data['rows']
    nodes = {int(k): v for k, v in data['prime_certificates'].items()}
    if len(rows) != 8742 or len(nodes) != 69609:
        raise ValueError('unexpected source table dimensions')
    if [r[0] for r in rows] != list(range(2001, 19484, 2)):
        raise ValueError('unexpected source order domain')
    OUT.mkdir(parents=True, exist_ok=True)
    generated = {}
    module_count = 0
    row_modules = []
    targets = set()
    for start in range(0, len(rows), ROWS_PER_BATCH):
        batch_no = start // ROWS_PER_BATCH
        batch = rows[start:start + ROWS_PER_BATCH]
        todo = [p for row in batch for p in row[3:]]
        targets.update(todo)
        pending = set()
        while todo:
            value = todo.pop()
            if value in generated or value in pending:
                continue
            if value not in nodes:
                raise ValueError(f'missing Lucas node {value}')
            pending.add(value)
            for q, exponent in nodes[value]['factors']:
                if not (type(q) is int and type(exponent) is int and 1 < q < value):
                    raise ValueError(f'invalid factor reference at {value}')
                todo.append(q)
        ordered = sorted(pending)
        for offset in range(0, len(ordered), MAX_NODES_PER_MODULE):
            values = ordered[offset:offset + MAX_NODES_PER_MODULE]
            name = f'N{module_count:04d}'
            dependencies = sorted({generated[q] for value in values
                for q, _ in nodes[value]['factors'] if q in generated})
            imports = ['import Sude.LucasCertificate']
            imports += [f'import Sude.GeneratedFTT.{dep}' for dep in dependencies]
            lines = imports + ['', '/-! Generated Lucas proof nodes; checked by Lean. -/',
                'namespace Sude.Lucas.Generated', 'set_option maxRecDepth 10000',
                'set_option maxHeartbeats 0', '']
            for value in values:
                cert = nodes[value]
                factors = cert['factors']
                if value == 2:
                    if cert != {'witness': 1, 'factors': []}:
                        raise ValueError('invalid base-node shape')
                    lines += ['theorem prime_2 : Nat.Prime 2 := Nat.prime_two', '']
                else:
                    if not factors:
                        raise ValueError(f'missing factors for {value}')
                    for q, _ in factors:
                        if q not in generated and q not in values[:values.index(value)]:
                            raise ValueError(f'factor {q} not earlier than {value}')
                    fac = ', '.join(f'({q}, {e})' for q, e in factors)
                    known = ', '.join(str(q) for q, _ in factors)
                    node = f'⟨{value}, {cert["witness"]}, [{fac}]⟩'
                    lines += [f'theorem prime_{value} : Nat.Prime {value} := by',
                        f'  apply nodeValid_prime [{known}] {node}',
                        '  · intro q hq',
                        '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq',
                        '    rcases hq with ' + ' | '.join('rfl' for _ in factors)]
                    if len(factors) == 1:
                        lines.append(f'    exact prime_{factors[0][0]}')
                    else:
                        lines += [f'    · exact prime_{q}' for q, _ in factors]
                    lines += ['  · decide +kernel', '']
            lines.append('end Sude.Lucas.Generated')
            (OUT / f'{name}.lean').write_text('\n'.join(lines) + '\n')
            generated.update({value: name for value in values})
            module_count += 1
        name = f'R{batch_no:04d}'
        dependencies = sorted({generated[p] for row in batch for p in row[3:]})
        lines = ['import Sude.FTTTargets']
        lines += [f'import Sude.GeneratedFTT.{dep}' for dep in dependencies]
        lines += ['', '/-! Generated exact FTT rows; pool X and T remain unproved. -/',
            'namespace Sude.Lucas.Generated', f'namespace {name}',
            'set_option maxRecDepth 10000', 'set_option maxHeartbeats 0', '']
        for row in batch:
            n, x, total, q, p, r = row
            literal = ', '.join(map(str, row))
            lines += [f'def row_{n} : TargetRow := ⟨{literal}⟩',
                f'theorem valid_{n} : TargetRowValid row_{n} := by',
                f'  dsimp [TargetRowValid, row_{n}]',
                f'  refine ⟨prime_{q}, prime_{p}, prime_{r}, ?_⟩',
                '  norm_num [absDiff]', '']
        lines += ['def rows : List TargetRow := [' + ', '.join(f'row_{r[0]}' for r in batch) + ']',
            '', 'theorem rows_valid : ∀ row ∈ rows, TargetRowValid row := by',
            '  intro row h',
            '  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h',
            '  rcases h with ' + ' | '.join('rfl' for _ in batch)]
        lines += [f'  · exact valid_{r[0]}' for r in batch]
        lines += ['', 'theorem orders : rows.map TargetRow.order =',
            f'    (List.range {len(batch)}).map (fun i => {batch[0][0]} + 2 * i) := by',
            '  decide +kernel', '', f'end {name}', 'end Sude.Lucas.Generated']
        (OUT / f'{name}.lean').write_text('\n'.join(lines) + '\n')
        row_modules.append(name)
    if set(nodes) != set(generated) or len(targets) != 25942:
        raise ValueError('generated graph is not the full FTT target closure')
    lines = [f'import Sude.GeneratedFTT.{name}' for name in row_modules]
    lines += ['', '/-! Complete generated FTT target rows; pool identities remain open. -/',
        'namespace Sude.Lucas.Generated', 'set_option maxRecDepth 10000',
        'def batches : List (List TargetRow) := [',
        ',\n'.join(f'  {name}.rows' for name in row_modules), ']',
        'def allRows : List TargetRow := batches.flatten', '',
        'theorem allRows_valid : ∀ row ∈ allRows, TargetRowValid row := by',
        '  intro row h', '  simp only [allRows, List.mem_flatten] at h',
        '  obtain ⟨batch, hbatch, hrow⟩ := h',
        '  simp only [batches, List.mem_cons, List.not_mem_nil, or_false] at hbatch',
        '  rcases hbatch with ' + ' | '.join('rfl' for _ in row_modules)]
    lines += [f'  · exact {name}.rows_valid row hrow' for name in row_modules]
    lines += ['', 'end Sude.Lucas.Generated']
    (OUT / 'All.lean').write_text('\n'.join(lines) + '\n')
    print(f'Generated {module_count} Lucas modules and {len(row_modules)} row modules; '
          f'{len(nodes)} nodes, {len(targets)} targets, {len(rows)} rows.')


if __name__ == '__main__':
    main()
