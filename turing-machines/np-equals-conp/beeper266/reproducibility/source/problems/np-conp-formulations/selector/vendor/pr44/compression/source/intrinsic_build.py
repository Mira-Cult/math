"""Pinned opt-in constant-add recipe for the complete streamed Horn source.

This selects four existing, semantics-preserving inherited intrinsics. It does
not change the source, kernel definitions, or integrated/countdown defaults.
The constructor is importable by the independent literal verification driver.
"""
from collections import Counter
from pathlib import Path
import argparse
import ast
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path[:0] = [str(HERE), str(ROOT / 'compression'),
               str(ROOT / 'compression/native'), str(ROOT / 'compression/grammar')]
from countdown import CountdownHornerBuilder
import fused_horner
import integrated_build

SOURCE = HERE / 'source_head_stream.py'
SOURCE_SHA256 = '1528e3762ba7dbfcd9e255c93ee058f313f6642799301a3b2351143d29a29cb2'
FULL_SITES = ('21:52:BinOp', '25:51:BinOp', '33:44:BinOp', '71:16:BinOp')
PATTERNS = {('k', 2): 2, ('n', 1): 1, ('program', 3): 1}
FLAGS = ('small_ops', 'small_compare', 'small_power', 'small_half')


def source_pin():
    text = SOURCE.read_text()
    if hashlib.sha256(text.encode()).hexdigest() != SOURCE_SHA256:
        raise ValueError('selected intrinsic recipe requires the frozen streamed source')
    return text


def check_comparison(text):
    """Accept only a paid main wrapper of this exact source comparison body.

    This mode is for finite-input validation tables, never for a complete
    beeper record. The complete recipe instead checks the full source hash.
    """
    original = next(node for node in ast.parse(source_pin()).body
                    if isinstance(node, ast.FunctionDef) and node.name == 'main')
    prefixes = []
    for loop in ast.walk(original):
        if isinstance(loop, ast.While):
            for position, node in enumerate(loop.body):
                if (isinstance(node, ast.If) and isinstance(node.test, ast.Name)
                        and node.test.id == 'expected'):
                    prefixes.append(loop.body[:position])
    if len(prefixes) != 1:
        raise ValueError('comparison extraction point changed')
    module = ast.parse(text)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise ValueError('expected one paid main fixture')
    main = module.body[0]
    if (main.name != 'main' or main.args.args or main.args.posonlyargs
            or main.args.kwonlyargs or main.args.vararg or main.args.kwarg
            or len(main.body) != 4 + len(prefixes[0]) + 2):
        raise ValueError('paid comparison wrapper shape')
    values = []
    for node, name in zip(main.body[:4], ('k', 'program', 'n', 'edges')):
        if not (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name) and node.targets[0].id == name
                and isinstance(node.value, ast.Constant)
                and type(node.value.value) is int and node.value.value >= 0):
            raise ValueError('paid comparison input constant')
        values.append(node.value.value)
    k, _, n, edges = values
    if k < 2 or n < 2 or edges >= 2 ** (n * n):
        raise ValueError('paid comparison input domain')
    if ([ast.dump(node) for node in main.body[4:-2]]
            != [ast.dump(node) for node in prefixes[0]]):
        raise ValueError('comparison body differs from frozen source')
    suffix = ast.parse('beep()\nreturn expected, clause, k, program, n, edges').body
    if [ast.dump(node) for node in main.body[-2:]] != [ast.dump(node) for node in suffix]:
        raise ValueError('fixture must keep outputs and preserved inputs live at its event')
    return values


def selected_sites(text, *, comparison=False):
    if comparison:
        check_comparison(text)
    elif hashlib.sha256(text.encode()).hexdigest() != SOURCE_SHA256:
        raise ValueError('complete recipe source hash mismatch')
    module = ast.parse(text)
    # The source repeats each divisor in its quotient/remainder tuple, but the
    # inherited consuming fusion evaluates only the first divisor AST. Check
    # precisely that syntax before excluding the second copy from selection.
    duplicate_divisors = set()
    for node in ast.walk(module):
        if not (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Tuple)
                and isinstance(node.value, ast.Tuple)):
            continue
        targets, values = node.targets[0].elts, node.value.elts
        if (len(targets) == len(values) == 2
                and all(isinstance(target, ast.Name) for target in targets)
                and targets[0].id != targets[1].id
                and isinstance(values[0], ast.BinOp) and isinstance(values[1], ast.BinOp)
                and isinstance(values[0].op, ast.Mod)
                and isinstance(values[1].op, ast.FloorDiv)
                and isinstance(values[0].left, ast.Name)
                and isinstance(values[1].left, ast.Name)
                and values[0].left.id == values[1].left.id
                and values[0].left.id in {target.id for target in targets}
                and ast.dump(values[0].right) == ast.dump(values[1].right)
                and not any(isinstance(child, ast.Call) for child in ast.walk(values[0].right))):
            duplicate_divisors.update(id(child) for child in ast.walk(values[1].right))
    found = {}
    counts = Counter()
    excluded = Counter()
    for node in ast.walk(module):
        if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)
                and isinstance(node.left, ast.Name) and isinstance(node.right, ast.Constant)
                and type(node.right.value) is int):
            continue
        key = (node.left.id, node.right.value)
        if key in PATTERNS:
            if id(node) in duplicate_divisors:
                excluded[key] += 1
                continue
            site = f'{node.lineno}:{node.col_offset}:BinOp'
            found[site] = {'expression': ast.unparse(node), 'op': 'Add',
                           'constant': node.right.value, 'operand': node.left.id}
            counts[key] += 1
    wanted = Counter(PATTERNS)
    if comparison:
        del wanted[('program', 3)]
    if counts != wanted:
        raise ValueError(('constant-add occurrence side condition', counts, wanted))
    if excluded != Counter({('k', 2): 2}):
        raise ValueError(('paired-divrem duplicate divisor side condition', excluded))
    if not comparison and set(found) != set(FULL_SITES):
        raise ValueError('complete source intrinsic positions changed')
    return found


class SelectedIntrinsicBuilder(CountdownHornerBuilder):
    """Same countdown/Horner builder, with precisely checked constant-add sites.

    ``comparison=True`` accepts only the paid comparison wrapper checked above.
    Every selected site must actually pass through the inherited intrinsic
    recognizer; syntax eligibility alone is not treated as a lowering receipt.
    """
    def __init__(self, text, *args, comparison=False, intrinsic_sites=(), **kwargs):
        self.selected_add_patterns = selected_sites(text, comparison=comparison)
        self.inherited_requested_sites = sorted(intrinsic_sites)
        self.actual_selected_patterns = {}
        self.selected_comparison = comparison
        for flag in FLAGS:
            if kwargs.get(flag, False) is not False:
                raise ValueError('global intrinsic flags are outside the selected recipe')
            kwargs[flag] = False
        if kwargs.get('countdown_loops', True) is not True:
            raise ValueError('selected recipe includes native countdown loops')
        kwargs['countdown_loops'] = True
        super().__init__(text, *args, intrinsic_sites=tuple(self.selected_add_patterns), **kwargs)

    def small_pattern(self, node):
        result = super().small_pattern(node)
        if result is not None:
            site = f"{getattr(node, 'lineno', None)}:{getattr(node, 'col_offset', None)}:{type(node).__name__}"
            record = {'expression': ast.unparse(node), 'op': result[1],
                      'constant': result[2], 'operand': ast.unparse(result[0])}
            if self.selected_add_patterns.get(site) != record:
                raise ValueError(('unexpected inherited intrinsic', site, record))
            self.actual_selected_patterns[site] = record
        return result

    def check_selected(self):
        if self.actual_selected_patterns != self.selected_add_patterns:
            raise ValueError(('selected intrinsic not visited', self.selected_add_patterns,
                              self.actual_selected_patterns))
        for site, pattern in self.selected_add_patterns.items():
            possible = self.possible_intrinsic_sites.get(site)
            if possible != {'expression': pattern['expression'],
                            'operation': 'Add', 'constant': pattern['constant']}:
                raise ValueError(('visited intrinsic evidence mismatch', site, possible))
        return self.actual_selected_patterns

    def build_tree(self):
        super().build_tree()
        self.check_selected()
        return self


def build(source, out):
    source, out = Path(source), Path(out)
    selected_sites(source.read_text())
    instances = []

    def constructor(*args, **kwargs):
        builder = SelectedIntrinsicBuilder(*args, **kwargs)
        instances.append(builder)
        return builder

    original = fused_horner.HornerBuilder
    try:
        fused_horner.HornerBuilder = constructor
        metadata = integrated_build.build(source, out, horner=True)
    finally:
        fused_horner.HornerBuilder = original
    if len(instances) != 1:
        raise ValueError('selected recipe constructor count')
    builder = instances[0]
    metadata['countdown_loops'] = True
    metadata['countdown_fusion'] = builder.countdown_certificate
    metadata['intrinsic_sites'] = sorted(builder.selected_add_patterns)
    metadata['actual_selected_intrinsics'] = builder.check_selected()
    metadata['possible_visited_intrinsics'] = builder.possible_intrinsic_sites
    metadata['inherited_expression_intrinsics'] = builder.intrinsic_certificate
    metadata['inherited_recipe_requested_parity_sites'] = metadata.pop('parity_sites')
    metadata['inherited_recipe_site_scope'] = 'overridden before lowering; these are not selected intrinsics'
    metadata['selected_recipe_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    metadata['lowering_sha256'] = {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (ROOT / 'compression/native/countdown.py',
                     ROOT / 'compression/grammar/fused_horner.py',
                     ROOT / 'compression/grammar/kernel_builder.py',
                     ROOT / 'accumulator/intrinsics.py')}
    metadata['review'] = 'producer recipe; independent source/kernel review and literal traces recorded separately'
    (out / 'metadata.json').write_text(json.dumps(metadata, sort_keys=True, indent=2) + '\n')
    return metadata


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=SOURCE)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = build(args.source, args.out)
    print(json.dumps({key: result[key] for key in ('states', 'rows', 'raw_states',
        'exact_states', 'registers', 'table_sha256', 'profile', 'actual_selected_intrinsics')},
        sort_keys=True, indent=2))
