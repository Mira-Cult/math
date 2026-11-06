"""Independent zero-run dispatcher refinement and full inherited certificates.

No producer compiler, dispatcher generator or completion solver is imported.
The unchanged source/storage/domain checkers are explicitly pinned dependencies.
"""
from copy import deepcopy
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
COMPACT = HERE.parents[2]
OLD = COMPACT / "phase_swap"
PRIOR = OLD / "review/binary/check_static.py"
PIN = "15562eff1257f63333bc711a3c2acbb7c50de05e6a462053da28945d87f76187"
PRODUCER = "7b90875183aa928fb19a4a9bf333b8ced2194ded"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


assert sha(PRIOR) == PIN
spec = importlib.util.spec_from_file_location("independent_repeated_control_phase_swap", PRIOR)
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)
base = prior.base


def named_rows(folder, names):
    reverse = {q: name for name, q in names.items()}
    assert len(reverse) == len(names)
    rows = base.completion.parse(Path(folder) / "raw.tm")[1]
    assert set(reverse) == set(range(len(rows) // 2))
    return {(reverse[q], bit): (write, move, reverse[target], event)
            for (q, bit), (write, move, target, event) in rows.items()}


def max_run(word):
    answer = run = 0
    for bit in word:
        assert bit in (0, 1)
        run = run + 1 if bit == 0 else 0
        answer = max(answer, run)
    return answer


def delimiter_rows(rows, limit):
    assert rows["6.continue.0", 0] == (0, "L", "6.continue.0", 0)
    assert rows["6.continue.0", 1] == (1, "L", "repeat.dispatch.0", 0)
    for counter in range(limit):
        name = "repeat.dispatch." + str(counter)
        target = "repeat.dispatch." + str(counter + 1) if counter + 1 < limit else "4.dispatch.scan"
        assert rows[name, 0] == (0, "L", target, 0)
        assert rows[name, 1] == (1, "L", "repeat.dispatch.0", 0)
    assert rows["4.dispatch.scan", 0] == (0, "R", "4.dispatch.scan", 0)
    assert rows["4.dispatch.scan", 1] == (1, "R", "5.root.1", 0)


def geometry(grammar, certificate):
    graph = base.endpoint.Graph(grammar)
    words = [(list(path), op) for path, op, *_ in graph.leaves]
    expected = [["".join(map(str, path)), op] for path, op in words]
    assert certificate["terminal_paths"] == expected
    limit = certificate["limit"]
    assert type(limit) is int and limit > 0
    maximum = max(max_run(path + [1, 0, 0]) for path, op in words)
    native = max(max_run(path + [1, 0]) for path, op in words)
    assert native <= maximum < limit
    assert certificate["max_prepared_zero_run"] == maximum
    assert certificate["max_path_length"] == max(len(path) for path, op in words)
    assert certificate["max_path_zeros"] == max(path.count(0) for path, op in words)
    digest = hashlib.sha256(json.dumps(expected, separators=(",", ":")).encode()).hexdigest()
    assert certificate["path_language_sha256"] == digest
    # Every actual lexical return and continue prefix is checked independently.
    returned = 0
    for path, op, *_ in graph.leaves:
        assert path[:3] == (1, 1, 0)
        for endpoint in range(3, len(path) + 1):
            assert max_run(path[:endpoint]) < limit
            if path[endpoint - 1] == 0:
                assert max_run(path[:endpoint - 1] + (1,)) < limit
            returned += 1
    return dict(terminal_occurrences=len(words), maximum_ordinary_prepared_zero_run=maximum,
                maximum_native_prepared_zero_run=native, delimiter_length=limit,
                checked_return_prefixes=returned, maximum_prepared_path=max(len(path) for path, op in words),
                maximum_path_zero_count=max(path.count(0) for path, op in words))


def runtime(parent, pdata):
    repo = next(path for path in HERE.parents if (path / "RESEARCH_PROTOCOL.md").is_file())
    old_parent = OLD / "machines/parent290"
    for filename in ("raw.tm", "names.json", "grammar.json"):
        path = old_parent / filename
        original = subprocess.check_output(["git", "-c", "protocol.allow=never", "show",
                                            PRODUCER + ":" + path.relative_to(repo).as_posix()], cwd=repo)
        assert original == path.read_bytes()
    old_names = load(old_parent / "names.json")
    names = pdata["names.json"]
    old_rows = named_rows(old_parent, old_names)
    rows = named_rows(parent, names)
    certificate = pdata["dispatcher.json"]
    assert pdata["grammar.json"] == load(old_parent / "grammar.json")
    checked_geometry = geometry(pdata["grammar.json"], certificate)
    limit = certificate["limit"]
    depth = max(path.count(0) for path, *_ in base.endpoint.Graph(pdata["grammar.json"]).leaves) + 2
    removed = {"4.dispatch." + str(i) for i in range(depth + 1)}
    added = {"repeat.dispatch." + str(i) for i in range(limit)}
    assert set(names) == (set(old_names) - removed) | added
    assert certificate["old_depth"] == depth
    assert certificate["old_dispatcher_states"] == len(removed)
    assert certificate["new_dispatcher_states"] == len(added)
    old_entry, new_entry = old_rows["6.continue.0", 1], rows["6.continue.0", 1]
    assert certificate["entry_before"] == [str(old_entry[0]), old_entry[1], old_entry[2]]
    assert certificate["entry_after"] == [str(new_entry[0]), new_entry[1], new_entry[2]]
    assert certificate["external_ingresses"] == [["6.continue.0", "1"]]
    actual_ingresses = [(name, str(bit)) for (name, bit), row in old_rows.items()
                        if row[2] in removed and name not in removed]
    assert actual_ingresses == [("6.continue.0", "1")]
    assert certificate["old_rows"] == [[name, bit, str(write), move, target]
        for (name, bit), (write, move, target, event) in sorted(old_rows.items()) if name in removed]
    assert certificate["new_rows"] == [[name, bit, str(write), move, target]
        for (name, bit), (write, move, target, event) in sorted(rows.items()) if name in added]
    unchanged = 0
    for key, row in rows.items():
        if key[0] in added or key == ("6.continue.0", 1):
            continue
        assert row == old_rows[key], key
        unchanged += 1
    delimiter_rows(rows, limit)
    # Source/lowering/storage/control are byte-identical replay outputs. The
    # new dispatcher changes no operation, bank address or ownership point.
    untouched = []
    for filename in ("allocation.json", "pre-control-grammar.json", "pre-projection-grammar.json",
                     "pre-coalescence-grammar.json", "grammar.json", "bank-projection.json",
                     "bank-coalescence.json", "coalescence-invariant.json", "control-certificate.json",
                     "contextual-tree-certificate.json", "native-runtime.json", "selector.json",
                     "three-move-swap.json", "direct-clock.json", "certificate-seed.json"):
        assert (Path(parent) / filename).read_bytes() == (old_parent / filename).read_bytes()
        untouched.append(filename)
    rejected = []
    def reject(label, function):
        try:
            function()
        except (AssertionError, KeyError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("damaged delimiter accepted: " + label)
    damaged = dict(rows)
    damaged["repeat.dispatch.1", 1] = (1, "L", "repeat.dispatch.1", 0)
    reject("failure to reset zero-run on one", lambda: delimiter_rows(damaged, limit))
    damaged = dict(rows)
    damaged["repeat.dispatch." + str(limit - 1), 0] = (0, "L", "repeat.dispatch.0", 0)
    reject("last zero never enters right scan", lambda: delimiter_rows(damaged, limit))
    damaged = dict(rows)
    damaged["6.continue.0", 1] = (1, "L", "repeat.dispatch.1", 0)
    reject("incorrect delimiter entry counter", lambda: delimiter_rows(damaged, limit))
    damaged_certificate = deepcopy(certificate)
    damaged_certificate["limit"] = certificate["max_prepared_zero_run"]
    reject("delimiter also occurs inside a prepared path", lambda: geometry(pdata["grammar.json"], damaged_certificate))
    damaged_certificate = deepcopy(certificate)
    damaged_certificate["terminal_paths"].pop()
    reject("omitted terminal path", lambda: geometry(pdata["grammar.json"], damaged_certificate))
    return dict(frozen_runtime_producer=PRODUCER, literally_identical_named_rows=unchanged,
                removed_countdown_states=len(removed), paid_delimiter_states=len(added),
                sole_changed_existing_row=["6.continue.0", 1],
                geometry=checked_geometry, untouched_semantic_artifacts=untouched,
                deliberate_delimiter_mutations_rejected=rejected,
                bootstrap_scope="unique blank-start finite initialization is independently executed and bound separately; ordinary path-language proof is not applied to intermediate boot tapes",
                proof="finite scan crosses no delimiter within any retained path/preparation; root110 resets zero-run and finite left blank supplies the delimiter; unchanged right scan reaches the same root with the whole tape unchanged")


def run(parent, selected, plan, source):
    old_runtime = prior.previous.runtime
    prior.previous.runtime = runtime
    try:
        result = prior.run(parent, selected, plan, source)
    finally:
        prior.previous.runtime = old_runtime
    result["format"] = "np-conp-repeated-control-independent-static-v1"
    result["reviewer"] = "internal-model-reviewer"
    result["authorship"] = "nonauthor of zero-run dispatcher, source, lowering, completion and tables"
    result["checker_sha256"] = sha(__file__)
    result["pinned_previous_checker_sha256"] = PIN
    result["damaged_certificates_rejected"] = [name for name in result["damaged_certificates_rejected"]
        if name != "incorrect parameterized dispatcher target"]
    result["damaged_certificates_rejected"] += result["runtime"]["deliberate_delimiter_mutations_rejected"]
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
