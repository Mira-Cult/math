"""Nonauthor literal-table and all-row-map checker; no producer imports.

This proves finite row equations, not reachability of any completion hole.
The latter requires the separately reviewed admitted-configuration invariant.
"""
from copy import deepcopy
from pathlib import Path
import argparse
import hashlib
import json


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def parse(path):
    headers, body = {}, []
    for line in Path(path).read_text().splitlines():
        if line.startswith("#! "):
            key, value = line[3:].split()
            assert key not in headers
            headers[key] = value
        else:
            body.append(line.split())
    assert headers["format"] in {"beeper-v1", "beeper-events-v1"}
    legacy = headers["format"] == "beeper-v1"
    assert set(headers) == ({"format", "states", "start", "blank", "head"}
                            | ({"beep"} if legacy else set()))
    count = int(headers["states"])
    start = int(headers["start"])
    assert count > 0 and start == 0
    assert headers["blank"] == headers["head"] == "0"
    beep = int(headers["beep"]) if legacy else None
    assert not legacy or 0 <= beep < count
    assert len(body) == 2 * count
    rows = {}
    for serial, fields in enumerate(body):
        assert len(fields) == (5 if legacy else 6)
        q, bit, write, move, target = fields[:5]
        q, bit, write, target = map(int, (q, bit, write, target))
        assert (q, bit) == divmod(serial, 2), "noncanonical row order"
        event = int(q == beep) if legacy else int(fields[5])
        assert write in (0, 1) and event in (0, 1)
        assert move in ("L", "R") and 0 <= target < count
        rows[q, bit] = (write, move, target, event)
    return headers, rows


def mapping(value, count):
    if isinstance(value, dict) and "mapping" in value:
        value = value["mapping"]
    if isinstance(value, dict):
        assert set(value) == {str(q) for q in range(count)}
        value = [value[str(q)] for q in range(count)]
    assert isinstance(value, list) and len(value) == count
    assert all(type(q) is int and q >= 0 for q in value)
    return value


def equations(before, after, mapped, ingress=False):
    bh, br = before
    ah, ar = after
    n, m = int(bh["states"]), int(ah["states"])
    mapped = mapping(mapped, n)
    assert set(mapped) == set(range(m))
    assert mapped[int(bh["start"])] == int(ah["start"])
    if ingress:
        assert bh["format"] == "beeper-v1"
        assert ah["format"] == "beeper-events-v1"
        beep = int(bh["beep"])
        assert int(bh["start"]) != beep
        assert all(br[beep, bit][2] != beep for bit in (0, 1))
    else:
        assert bh["format"] == ah["format"]
        if "beep" in bh:
            beep, new_beep = int(bh["beep"]), int(ah["beep"])
            assert mapped[beep] == new_beep
            assert [q for q in range(n) if mapped[q] == new_beep] == [beep]
    for (q, bit), (write, move, target, event) in br.items():
        expected_event = int(target == beep) if ingress else event
        assert ar[mapped[q], bit] == (write, move, mapped[target], expected_event), (q, bit)
    return len(br)


def bundle(folder):
    folder = Path(folder)
    raw, companion, events = [parse(folder / name) for name in ("raw.tm", "machine.tm", "events.tm")]
    quotient = load(folder / "quotient.json")
    event_map = load(folder / "event-quotient.json")
    ordinary = equations(raw, companion, quotient)
    marked = equations(companion, events, event_map, ingress=True)
    literal_ingress = parse(folder / "ingress-prequotient.tm")
    identity = list(range(int(companion[0]["states"])))
    equations(companion, literal_ingress, identity, ingress=True)
    result = dict(states={name: int(table[0]["states"])
                          for name, table in (("raw", raw), ("B", companion), ("marked", events))},
                  ordinary_row_equations=ordinary, ingress_row_equations=marked,
                  sole_or_multiple_marked_rows=[[q, bit, *row] for (q, bit), row in events[1].items() if row[3]],
                  hashes={name: sha(folder / name) for name in ("raw.tm", "machine.tm", "events.tm", "quotient.json", "event-quotient.json", "ingress-prequotient.tm")})
    return result


def completion(parent, selected):
    parent, selected = Path(parent), Path(selected)
    control = parse(parent / "machine.tm")
    completed = parse(selected / "raw.tm")
    assert control[0] == completed[0]
    domain = load(selected / "domain.json")
    assert domain["control_sha256"] == sha(parent / "machine.tm")
    assert domain["raw_quotient_sha256"] == sha(parent / "quotient.json")
    assert domain["names_sha256"] == sha(parent / "names.json")
    holes = {tuple(pair) for pair in domain["holes"]}
    assert len(holes) == len(domain["holes"])
    assert holes <= control[1].keys()
    differences = {key for key in control[1] if control[1][key] != completed[1][key]}
    assert differences <= holes
    raw = parse(parent / "raw.tm")
    mapped = mapping(load(parent / "quotient.json"), int(raw[0]["states"]))
    preimages = {str(q): [r for r in range(len(mapped)) if mapped[r] == q] for q, bit in holes}
    assert domain["preimages"] == preimages
    assert all(preimages[str(q)] for q, bit in holes)
    occurrences = sum(len(preimages[str(q)]) for q, bit in holes)
    return dict(retained_row_equations=len(control[1]) - len(holes),
                declared_holes=len(holes), actually_different_rows=len(differences),
                raw_preimage_row_occurrences=occurrences,
                scope="hole inventory and every raw preimage; semantic unreachability is a separate obligation")


def mutations(folder):
    folder = Path(folder)
    before, after = parse(folder / "machine.tm"), parse(folder / "events.tm")
    original = mapping(load(folder / "event-quotient.json"), int(before[0]["states"]))
    rejected = []
    def reject(label, a, b, m):
        try:
            equations(a, b, m, ingress=True)
        except (AssertionError, KeyError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("damaged row/map accepted: " + label)
    event_key = next(key for key, row in after[1].items() if row[3])
    for component, value in ((0, 1 - after[1][event_key][0]),
                             (1, "R" if after[1][event_key][1] == "L" else "L"),
                             (2, (after[1][event_key][2] + 1) % int(after[0]["states"])),
                             (3, 0)):
        bad = deepcopy(after)
        row = list(bad[1][event_key]); row[component] = value
        bad[1][event_key] = tuple(row)
        reject("marked row component " + str(component), before, bad, original)
    bad = deepcopy(after); del bad[1][event_key]
    reject("missing marked branch", before, bad, original)
    bad = list(original); bad[0] = (bad[0] + 1) % int(after[0]["states"])
    reject("wrong initial quotient map", before, after, bad)
    return rejected


def run(parent, selected):
    return dict(format="np-conp-repeated-control-independent-rows-v1",
                reviewer="internal-model-reviewer; nonauthor of producer",
                parent=bundle(parent), selected=bundle(selected),
                completion=completion(parent, selected),
                deliberate_mutations_rejected=mutations(selected),
                checker_sha256=sha(__file__),
                scope="complete literal structure, all ordinary and ingress-event row equations, retained completion rows and raw fibers; no reachability or mathematical endpoint inferred")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("parent", "selected", "out"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = run(args.parent, args.selected)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("completion", "deliberate_mutations_rejected")}, sort_keys=True))
