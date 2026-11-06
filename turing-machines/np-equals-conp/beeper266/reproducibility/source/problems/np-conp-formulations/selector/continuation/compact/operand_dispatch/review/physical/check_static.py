"""Nonauthor control-mode selector, domain, storage and row-map review."""
from copy import deepcopy
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess

HERE = Path(__file__).resolve().parent
COMPACT = HERE.parents[2]
PREVIOUS = COMPACT / "repeated_control/review/physical/check_static.py"
PIN = "96d45c10095cec2ad2f66e23f0906bc968ce386d002c2f9c6b8cd869e3d6a5e5"
CONTROL = COMPACT / "repeated_control/machines/zero_run6_parent"
CONTROL_PRODUCER = "0461db7d761cb34ff1e773c5d4dbe2cfd9c1235a"
EXCLUDED = {"1b.reg.prep_1": 1, "2h.native_half.begin": 0,
            "2h.native_half.boundary": 1, "2h.native_half.prep": 1,
            "2h.native_half.undo": 0}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


assert sha(PREVIOUS) == PIN
spec = importlib.util.spec_from_file_location("independent_operand_previous", PREVIOUS)
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)
prior, base = previous.prior, previous.base


def selector_rows(rows, order):
    assert rows["1b.reg.prep_1", 0] == (0, "R", "1b.reg.prep_2", 0)
    assert rows["1b.reg.prep_2", 0] == (1, "R", "1b.reg.prep_2", 0)
    assert rows["1b.reg.prep_2", 1] == (1, "L", "6.continue.0", 0)
    for index, register in enumerate(order):
        for mode, suffix in (("inc", "inc"), ("dec", "decnz")):
            operation = "3." + register + "." + suffix
            assert rows[operation, 0] == (1, "R", "1b.reg.prep_1", 0)
            assert rows[operation, 1] == (0, "R", f"2b.reg.{index}.{mode}", 0)
            name = f"2b.reg.{index}.{mode}"
            assert rows[name, 0] == (0, "R", f"2b.reg.{index - 1}.{mode}", 0)
            assert rows[name, 1] == (1, "R", name, 0)
    for mode in ("inc", "dec"):
        assert rows[f"2b.reg.-1.{mode}", 0] == (0, "R", f"2b.reg.-2.{mode}", 0)
        assert rows[f"2b.reg.-1.{mode}", 1] == (1, "R", f"2b.reg.-1.{mode}", 0)
    first = order[0]
    assert rows["0a.boot1.C", 1] == (1, "R", "3." + first + ".inc", 0)
    assert rows["0b.boot2.2", 0] == (0, "R", "3." + first + ".inc", 0)
    assert rows["0b.boot2.2", 1] == (1, "R", "3." + first + ".decnz", 0)


def runtime(parent, data):
    repo = next(p for p in HERE.parents if (p / "RESEARCH_PROTOCOL.md").is_file())
    for filename in ("raw.tm", "names.json", "grammar.json"):
        path = CONTROL / filename
        assert path.read_bytes() == subprocess.check_output(
            ["git", "-c", "protocol.allow=never", "show",
             CONTROL_PRODUCER + ":" + path.relative_to(repo).as_posix()], cwd=repo)
    names = data["names.json"]
    old_names = load(CONTROL / "names.json")
    rows = previous.named_rows(parent, names)
    old_rows = previous.named_rows(CONTROL, old_names)
    order = data["grammar.json"]["registers"]
    assert data["grammar.json"] == load(CONTROL / "grammar.json")
    assert len(order) == 12
    removed = {name for name in old_names if name.startswith("shared.selector.")}
    added = {f"2b.reg.{i}.{kind}" for i in range(1, len(order)) for kind in ("inc", "dec")}
    assert len(removed) == 31 and len(added) == 22
    assert set(names) == (set(old_names) - removed) | added
    changed = {(f"3.{register}.{kind}", 1) for register in order for kind in ("inc", "decnz")}
    changed |= {("0a.boot1.C", 1), ("0b.boot2.2", 0), ("0b.boot2.2", 1), ("1b.reg.prep_1", 0)}
    unchanged = 0
    for key, row in rows.items():
        if key[0] in added or key in changed:
            continue
        assert row == old_rows[key], key
        unchanged += 1
    assert unchanged == 482
    selector_rows(rows, order)
    actual_changed = {key for key in rows.keys() & old_rows.keys() if rows[key] != old_rows[key]}
    assert actual_changed == changed
    selector = data["selector.json"]
    assert selector["kind"] == "np-conp-control-mode-selector-v1"
    assert selector["registers"] == len(order)
    assert set(map(tuple, selector["new_totalized_rows"])) == {(name, str(bit)) for name, bit in EXCLUDED.items()}
    expected_entries = [dict(register=register, index=index, operation=mode,
                             terminal=f"3.{register}.{suffix}")
        for index, register in enumerate(order) for mode, suffix in (("inc", "inc"), ("dec", "decnz"))]
    assert selector["operation_entries"] == expected_entries
    geometry = previous.geometry(data["grammar.json"], data["dispatcher.json"])
    previous.delimiter_rows(rows, data["dispatcher.json"]["limit"])
    full_paths = [path for path, *_ in base.endpoint.Graph(data["grammar.json"]).leaves]
    actual_run = max(previous.max_run(path + (1, 0)) for path in full_paths)
    assert actual_run < data["dispatcher.json"]["limit"] == 6
    assert data["dispatcher.json"]["old_depth"] == max(path.count(0) for path in full_paths) + 1 == 12
    natives = data["native-runtime.json"]["operands"]
    assert order[:len(natives)] == natives
    for index, register in enumerate(natives):
        operation = "3.$native-half:" + register + ".decnz"
        assert rows[operation, 0] == (1, "R", "2h.native_half.prep", 0)
        assert rows[operation, 1] == (0, "R", "2h.native_half.select." + str(index), 0)
    unchanged_artifacts = []
    for filename in ("allocation.json", "pre-control-grammar.json", "pre-projection-grammar.json",
                     "pre-coalescence-grammar.json", "grammar.json", "bank-projection.json",
                     "bank-coalescence.json", "coalescence-invariant.json", "control-certificate.json",
                     "contextual-tree-certificate.json", "native-runtime.json", "native-half.json",
                     "three-move-swap.json", "direct-clock.json", "certificate-seed.json", "whole-action.json"):
        assert (Path(parent) / filename).read_bytes() == (CONTROL / filename).read_bytes(), filename
        unchanged_artifacts.append(filename)
    rejected = []
    def reject(label, damaged):
        try:
            selector_rows(damaged, order)
        except (AssertionError, KeyError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("damaged selector accepted: " + label)
    damaged = dict(rows)
    damaged["3." + order[1] + ".inc", 1] = (0, "R", "2b.reg.0.inc", 0)
    reject("wrong operand distance", damaged)
    damaged = dict(rows)
    damaged["3." + order[1] + ".decnz", 1] = (0, "R", "2b.reg.1.inc", 0)
    reject("wrong operation kind", damaged)
    damaged = dict(rows)
    damaged["3." + order[1] + ".decnz", 1] = (1, "R", "2b.reg.1.dec", 0)
    reject("unremoved tape mode bit", damaged)
    damaged = dict(rows)
    damaged["1b.reg.prep_1", 0] = (0, "R", "1b.reg.prep_1", 0)
    reject("incorrect preparation gap", damaged)
    damaged = dict(rows)
    damaged["0b.boot2.2", 1] = (1, "R", "3." + order[0] + ".inc", 0)
    reject("wrong bootstrap operation", damaged)
    return dict(frozen_runtime_producer=CONTROL_PRODUCER,
                exact_common_named_rows=unchanged, explicitly_changed_existing_rows=len(changed),
                removed_shared_selector_states=len(removed), added_control_mode_states=len(added),
                ordinary_operation_entries=2 * len(order), native_operation_entries=len(natives),
                preparation_zero_cells=1, operation_and_address_paid_in_control=True,
                delimiter_geometry=geometry, actual_one_zero_prepared_max_run=actual_run,
                unchanged_source_storage_artifacts=unchanged_artifacts,
                semantic_exclusions=[[name, bit] for name, bit in sorted(EXCLUDED.items())],
                selector_mutations_rejected=rejected,
                proof_scope="one-zero preparation; each zero decrements finite field distance without changing operation mode; unchanged -2 INC/DECNZ kernel and HALF/return contracts; separately checked unique blank initialization")


def run(parent, selected, plan, source):
    old_runtime, old_excluded = prior.previous.runtime, base.completion.EXCLUDED
    prior.previous.runtime, base.completion.EXCLUDED = runtime, EXCLUDED
    try:
        result = prior.run(parent, selected, plan, source)
    finally:
        prior.previous.runtime, base.completion.EXCLUDED = old_runtime, old_excluded
    result["format"] = "np-conp-control-mode-independent-static-v1"
    result["reviewer"] = "internal-model-reviewer; nonauthor of producer"
    result["authorship"] = "independent of control-mode selector, source, lowering, completion and tables"
    result["checker_sha256"] = sha(__file__)
    result["pinned_previous_dispatch_checker_sha256"] = PIN
    result["damaged_certificates_rejected"] = [x for x in result["damaged_certificates_rejected"]
        if x != "incorrect parameterized dispatcher target"]
    result["damaged_certificates_rejected"] += result["runtime"]["selector_mutations_rejected"]
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("parent", "selected", "plan", "source", "out"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = run(args.parent, args.selected, args.plan, args.source)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("runtime", "completion", "damaged_certificates_rejected")}, sort_keys=True, indent=2))
