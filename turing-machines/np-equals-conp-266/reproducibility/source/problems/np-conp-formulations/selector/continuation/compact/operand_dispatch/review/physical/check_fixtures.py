"""Independent one-zero ABI adapter to the pinned nonauthor fixture harness.

Exactly two AST changes adapt the previous prepared-tape convention. Expected
arithmetic, full tapes, return paths and row-map checks remain reviewer-owned.
No producer or authored fixture module is imported.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import sys
import types

HERE = Path(__file__).resolve().parent
COMPACT = HERE.parents[2]
PRIOR = COMPACT / "transfer328/review/binary/check_fixtures.py"
PIN = "7f74efa1cae809e38ceb1265035ef15e8e0d1397523381143459a74b35907940"
HELPER_PIN = "40a6aabb3bfb7fab72c667962bcccc3c86415841cb858f9dcc71fa0003cf9e5f"
EXCLUDED = {"1b.reg.prep_1": 1, "2h.native_half.begin": 0,
            "2h.native_half.boundary": 1, "2h.native_half.prep": 1,
            "2h.native_half.undo": 0}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def harness():
    assert sha(PRIOR) == PIN
    assert sha(PRIOR.with_name("check_static.py")) == HELPER_PIN
    tree = ast.parse(PRIOR.read_text())
    patches = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name) and node.targets[0].id == "pad":
            assert ast.dump(node.value, include_attributes=False) == ast.dump(ast.parse("2 if kind == 'half' else 3", mode="eval").body, include_attributes=False)
            node.value = ast.Constant(2)
            patches.append("all operation fixture gaps have one separator zero")
        if isinstance(node, ast.For) and ast.dump(node.target, include_attributes=False) == ast.dump(ast.parse("name,pads=0").body[0].targets[0], include_attributes=False):
            assert ast.literal_eval(node.iter) == [("1b.reg.prep_1", 2), ("2h.native_half.prep", 1), ("shared.selector.bootstrap.prep", 1)]
            node.iter = ast.parse("[('1b.reg.prep_1',1),('2h.native_half.prep',1)]", mode="eval").body
            patches.append("ordinary/native one-zero preparation; removed shared bootstrap adapter")
    assert len(patches) == 2
    ast.fix_missing_locations(tree)
    module = types.ModuleType("independent_control_mode_fixture_harness")
    module.__file__ = str(PRIOR)
    sys.path.insert(0, str(PRIOR.parent))
    exec(compile(tree, str(PRIOR), "exec"), vars(module))
    module.SEMANTIC_EXCLUSIONS = EXCLUDED
    return module, patches


def run(parent, selected):
    previous, patches = harness()
    result = previous.check(parent, selected)
    result["format"] = "np-conp-control-mode-independent-injected-v1"
    result["reviewer"] = "internal-model-reviewer; nonauthor of selector, source, lowering, completion and tables"
    result["wrapper_sha256"] = sha(__file__)
    result["pinned_harness_sha256"] = PIN
    result["pinned_helper_sha256"] = HELPER_PIN
    result["explicit_reviewed_adaptations"] = patches
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("parent", "selected", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    result = run(args.parent, args.selected)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("injected_cases", "literal_steps", "grammar_occurrences")}, sort_keys=True))
