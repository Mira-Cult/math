"""Independent exact maps, abstract storage and dual-engine endpoint review.

No producer/compiler module is imported. Grammar paths, native value transfer,
bank decoding and table maps are reviewer-owned; literal engines are the
previously pinned independently authored C++ deque and C11 bitset programs.
"""
from collections import deque
from copy import deepcopy
from pathlib import Path
import argparse
import hashlib
import inspect
import json
import subprocess


HERE = Path(__file__).resolve().parent
TAPE = HERE.parents[1]
COMPACT = TAPE.parent
PRIOR = COMPACT.parent / "review/independent"
ENGINE_PINS = {
    "literal_review.cpp": "6506be2c128572420d44d9c12e2811f25d3618c50dc199b23eba6d9918f04bff",
    "literal_bitset.c": "0fdf891700a548a6144a4b6780483743ce5676b17e7f696f65ffeb4841e8c5e6",
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def jd(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def operand(operation):
    assert operation.startswith("3.")
    value = operation[2:]
    for mode, suffix in (("half", ".decnz"), ("double", ".inc"), ("push1", ".inc")):
        prefix = "$native-" + mode + ":"
        if value.startswith(prefix):
            assert value.endswith(suffix)
            return mode, value[len(prefix):-len(suffix)]
    name, kind = value.rsplit(".", 1)
    assert kind in ("inc", "decnz")
    return kind, name


def renamed(operation, mapping):
    if not operation.startswith("3."):
        return operation
    kind, name = operand(operation)
    if kind in ("inc", "decnz"):
        return "3." + mapping[name] + "." + kind
    return "3.$native-" + kind + ":" + mapping[name] + (".decnz" if kind == "half" else ".inc")


def value_step(kind, value):
    if kind == "inc":
        return value+1, 0
    if kind == "decnz":
        return max(value-1, 0), int(value == 0)
    if kind == "half":
        return value//2, int(value % 2 == 0)
    if kind == "double":
        return value*2, 0
    assert kind == "push1"
    return value*2+1, 0


class Graph:
    def __init__(self, grammar):
        self.grammar = grammar
        self.nodes = grammar["nodes"]
        self.root = grammar["root"]
        self.leaves = []

        def visit(node, path, ancestors):
            assert node not in ancestors
            assert len(self.nodes[node]) == 2
            for bit, child in enumerate(self.nodes[node]):
                assert set(child) in ({"node"}, {"op"})
                if "node" in child:
                    visit(child["node"], path+(bit,), ancestors | {node})
                else:
                    self.leaves.append((path+(bit,), child["op"], node, bit))
        visit(self.root, (1, 1, 0), set())
        self.by_path = {path: i for i, (path, *_) in enumerate(self.leaves)}
        assert len(self.by_path) == len(self.leaves)
        self.rows = []
        for path, op, node, bit in self.leaves:
            if op.startswith("_break."):
                targets = (self.returned(path, int(op.split(".")[1])),)
            elif op.startswith("_continue."):
                skip = int(op.split(".")[1])
                found = None
                for i in range(len(path)-1, 0, -1):
                    if path[i] == 1:
                        if skip:
                            skip -= 1
                        else:
                            found = self.resolve(path[:i+1])
                            break
                assert found is not None
                targets = (found,)
            elif op == "beep":
                targets = (self.returned(path, 0),)
            else:
                kind, name = operand(op)
                assert name in grammar["registers"]
                targets = (self.returned(path, 0),)
                if kind in ("half", "decnz"):
                    targets += (self.returned(path, 1),)
            self.rows.append((op, *targets))
        self.entry = self.resolve((1, 1, 0))

    def resolve(self, path):
        if path[:3] == (1, 1, 1):
            path = (1, 1, 0)
        path = path + (0,)*max(0, 3-len(path))
        node, index = self.root, 3
        while True:
            if index == len(path):
                path += (0,)
            child = self.nodes[node][path[index]]
            index += 1
            if "op" in child:
                assert index == len(path)
                return self.by_path[path]
            node = child["node"]

    def returned(self, path, skip):
        for i in range(len(path)-1, 1, -1):
            if path[i] == 0:
                if skip:
                    skip -= 1
                else:
                    return self.resolve(path[:i]+(1,))
        raise AssertionError("return escaped root")

    def core(self, mapping=None):
        def contract(position):
            seen = set()
            while self.rows[position][0].startswith(("_break.", "_continue.")):
                assert position not in seen, "administrative cycle"
                seen.add(position)
                position = self.rows[position][1]
            return position
        for position in range(len(self.rows)):
            contract(position)
        entry = contract(self.entry)
        ids, work, out = {entry: 0}, deque([entry]), []
        while work:
            position = work.popleft()
            op, *targets = self.rows[position]
            targets = [contract(target) for target in targets]
            for target in targets:
                if target not in ids:
                    ids[target] = len(ids)
                    work.append(target)
            out.append([renamed(op, mapping) if mapping is not None else op,
                        *[ids[target] for target in targets]])
        return dict(entry=0, rows=out)

    def events(self, wanted):
        values = dict.fromkeys(self.grammar["registers"], 0)
        position, out, native = self.entry, [], 0
        for steps in range(10_000_000):
            op, *targets = self.rows[position]
            if op == "beep":
                out.append(dict(values))
                if len(out) == wanted:
                    return out, dict(steps=steps+1, native_operations=native)
                position = targets[0]
            elif op.startswith(("_break.", "_continue.")):
                position = targets[0]
            else:
                kind, name = operand(op)
                native += int(kind in ("half", "double", "push1"))
                values[name], outcome = value_step(kind, values[name])
                position = targets[outcome]
        raise AssertionError("finite grammar fixture exceeded budget")


def closure(grammar, invariant):
    graph = Graph(grammar)
    assert invariant["input_grammar"] == grammar
    assert invariant["input_grammar_sha256"] == jd(grammar)
    states = invariant["states_at_occurrences"]
    assert len(states) == len(graph.rows)
    names = grammar["registers"]
    for state in states:
        assert state is None or len(state) == len(names) and set(state) <= set("1234567")
    assert states[graph.entry] is not None and all(int(m) & 1 for m in states[graph.entry])
    total = 0
    for index, (op, *targets) in enumerate(graph.rows):
        encoded = states[index]
        if encoded is None:
            continue
        state = list(map(int, encoded))
        if op == "beep" or op.startswith(("_break.", "_continue.")):
            images = {targets[0]: state}
        else:
            kind, name = operand(op)
            slot = names.index(name)
            # These representatives exhaust zero/one/many images for each
            # reviewed arithmetic map and each success/failure outcome.
            images = {}
            for value in range(8):
                mask = 1 if value == 0 else 2 if value == 1 else 4
                if not state[slot] & mask:
                    continue
                after, branch = value_step(kind, value)
                result = 1 if after == 0 else 2 if after == 1 else 4
                target = targets[branch]
                if target not in images:
                    images[target] = list(state)
                    images[target][slot] = 0
                images[target][slot] |= result
        for target, image in images.items():
            assert states[target] is not None
            assert all(not (a & ~int(b)) for a, b in zip(image, states[target])), (index, op, target)
            total += 1
    return graph, dict(occurrences=len(graph.rows), closed_edges=total)


def storage(folder):
    before = read(folder/"pre-projection-grammar.json")
    projected = read(folder/"pre-coalescence-grammar.json")
    final = read(folder/"grammar.json")
    projection = read(folder/"bank-projection.json")
    sharing = read(folder/"bank-coalescence.json")
    invariant = read(folder/"coalescence-invariant.json")
    context = read(folder/"contextual-tree-certificate.json")
    _, context_closure = closure(context["input_grammar"], context)
    assert context["output_grammar_sha256"] == jd(before)
    assert projection["before_grammar_sha256"] == jd(before)
    assert projection["after_grammar_sha256"] == jd(projected)
    assert {k:v for k,v in before.items() if k != "registers"} == {k:v for k,v in projected.items() if k != "registers"}
    used, halves = set(), set()
    for pair in before["nodes"]:
        for child in pair:
            op = child.get("op", "")
            if op.startswith("3."):
                kind, name = operand(op)
                used.add(name)
                if kind == "half":
                    halves.add(name)
    old = before["registers"]
    if not used:
        used.add(old[0])
    retained = [name for name in old if name in halves] + [name for name in old if name in used and name not in halves]
    removed = [name for name in old if name not in used]
    assert projected["registers"] == retained == projection["retained_register_order"]
    assert projection["removed_registers"] == removed
    assert projection["removed_interpretation"] == dict.fromkeys(removed, 0)
    assert projection["old_to_new"] == [retained.index(name) if name in retained else None for name in old]
    graph, shared_closure = closure(projected, invariant)
    assert sharing["before_grammar_sha256"] == jd(projected)
    assert sharing["after_grammar_sha256"] == jd(final)
    assert sharing["invariant_sha256"] == jd(invariant)
    groups = sharing["groups"]
    flattened = [name for members in groups.values() for name in members]
    assert all(groups.values()) and len(flattened) == len(set(flattened)) == len(retained)
    assert set(flattened) == set(retained)
    assert set(groups) == set(final["registers"])
    mapping = {name:key for key,members in groups.items() for name in members}
    assert mapping == sharing["mapping"]
    checked, peer_sites = 0, 0
    for index, (op, *_) in enumerate(graph.rows):
        state = invariant["states_at_occurrences"][index]
        if state is None or not op.startswith("3."):
            continue
        _, name = operand(op)
        peers = [other for other in groups[mapping[name]] if other != name]
        assert all(state[retained.index(other)] == "1" for other in peers)
        checked += 1
        peer_sites += bool(peers)
    assert checked == sharing["all_reached_operations_checked"]
    assert graph.core(mapping) == Graph(final).core()
    bad = deepcopy(invariant)
    initial = list(bad["states_at_occurrences"][graph.entry])
    initial[0] = "2"
    bad["states_at_occurrences"][graph.entry] = "".join(initial)
    try:
        closure(projected, bad)
    except AssertionError:
        pass
    else:
        raise AssertionError("false initial abstract fact escaped")
    damaged = deepcopy(final)
    for pair in damaged["nodes"]:
        if any(child.get("op") == "beep" for child in pair):
            for child in pair:
                if child.get("op") == "beep":
                    child["op"] = "_break.0"
            break
    assert graph.core(mapping) != Graph(damaged).core(), "deleted event escaped"
    return dict(contextual_closure=context_closure, sharing_closure=shared_closure,
                original_cells=len(old), projected_cells=len(retained), physical_cells=len(final["registers"]),
                operation_zero_peer_checks=checked, nontrivial_peer_sites=peer_sites,
                independently_mapped_core_sha256=jd(graph.core(mapping)),
                removed_zero_coordinates=removed,
                scope="Independent native-aware abstract closure, unused-cell projection, zero-peer premises and full retained graph equality. Local contextual rewrite algebra and source allocation have separate review.")


def table(path):
    header, rows = {}, {}
    for line in path.read_text().splitlines():
        if line.startswith("#! "):
            key, value = line[3:].split()
            assert key not in header
            header[key] = value
            continue
        items = line.split()
        assert len(items) == (5 if header["format"] == "beeper-v1" else 6)
        q, z, w = map(int, items[:3])
        move, target = items[3], int(items[4])
        event = int(items[5]) if len(items) == 6 else int(q == int(header["beep"]))
        assert (q,z) not in rows and z in (0,1) and w in (0,1) and event in (0,1)
        assert move in ("L", "R")
        rows[q,z] = (w,move,target,event)
    count = int(header["states"])
    assert set(rows) == {(q,z) for q in range(count) for z in (0,1)}
    assert all(0 <= row[2] < count for row in rows.values())
    assert header["start"] == header["head"] == header["blank"] == "0"
    return header, rows


def mapped(mapping, q):
    return mapping[q] if isinstance(mapping, list) else mapping[str(q)]


def row_maps(folder):
    tables = [table(folder/name) for name in ("raw.tm", "machine.tm", "ingress-prequotient.tm", "events.tm")]
    (rh,raw),(bh,companion),(ih,ingress),(eh,event) = tables
    bmap = read(folder/"quotient.json")
    emap = read(folder/"event-quotient.json")["mapping"]
    assert mapped(bmap,0) == mapped(emap,0) == 0
    assert set(mapped(bmap,q) for q in range(int(rh["states"]))) == set(range(int(bh["states"])))
    assert set(mapped(emap,q) for q in range(int(bh["states"]))) == set(range(int(eh["states"])))
    for (q,z),(w,m,t,e) in raw.items():
        assert companion[mapped(bmap,q),z] == (w,m,mapped(bmap,t),e)
    for (q,z),(w,m,t,e) in companion.items():
        expected = int(t == int(bh["beep"]))
        assert ingress[q,z] == (w,m,t,expected)
        assert event[mapped(emap,q),z] == (w,m,mapped(emap,t),expected)
    assert bh["start"] != bh["beep"]
    return bmap, emap, dict(raw=int(rh["states"]), B_exit=int(bh["states"]), marked=int(eh["states"]),
                           rows=[len(raw),len(companion),len(event)],
                           marked_rows=[[q,z,*row] for (q,z),row in event.items() if row[3]])


def bank(ones, count):
    ones = set(ones)
    position, values, widths = 9, [], []
    for _ in range(count):
        value, width = 0, 0
        while position in ones:
            if position+1 in ones:
                value += 1 << width
            width += 1
            position += 2
        assert width and position+1 not in ones
        values.append(value)
        widths.append(width)
        position += 2
    return values, widths, position


def source_events(path, wanted):
    events = []
    class Enough(Exception):
        pass
    def beep():
        events.append(dict(inspect.currentframe().f_back.f_locals))
        if len(events) == wanted:
            raise Enough
    namespace = {"beep": beep}
    exec(compile(path.read_text(), str(path), "exec"), namespace)
    try:
        namespace["main"]()
    except Enough:
        return events
    raise AssertionError("source stopped before requested finite event prefix")


def transducer_fixtures(folder):
    _, rows = table(folder/"raw.tm")
    names = read(folder/"names.json")
    observations = []
    for initial_units in (1,2,3,5,10,31,64,129):
        left = -(2*initial_units+1)
        ones = set(range(left,-2,2)) | {-2,0,1,2,3}
        state, head = names["binary.direct_bootstrap.entry"], -2
        for steps in range(100*(initial_units+2)**2+1000):
            if state == names["main().0"]:
                break
            write, move, state, event = rows[state,int(head in ones)]
            assert event == 0
            if write:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if move == "R" else -1
        else:
            raise AssertionError("finite transducer fixture exhausted budget")
        expected = {left-1,left,3} | set(range(9,9+4*(initial_units-1),4))
        assert (head,ones) == (left+2,expected)
        observations.append(dict(initial_alternating_units=initial_units,output_zero_fields=initial_units-1,
                                 steps=steps,head=head,whole_configuration_sha256=jd([state,head,sorted(ones)])))
    return observations


def real_boundary_trace(folder, entry, expected_final):
    """Resume the exact actual blank-run checkpoint, not a synthetic entry."""
    header, raw = table(folder/"raw.tm")
    rows = [raw[q,z] for q in range(int(header["states"])) for z in (0,1)]
    rows = [(w,1 if m == "R" else -1,t,e) for w,m,t,e in rows]
    names = read(folder/"names.json")
    observed_names = {}
    for name, state in names.items():
        if name == "beep" or name.startswith("3."):
            assert state not in observed_names
            observed_names[state] = name
    ghost = read(folder/"pre-coalescence-grammar.json")
    graph = Graph(ghost)
    sharing = read(folder/"bank-coalescence.json")
    groups, mapping = sharing["groups"], sharing["mapping"]
    order = read(folder/"grammar.json")["registers"]
    capacity = read(folder/"binary-runtime.json")["zero_register_capacity"]
    values = dict.fromkeys(ghost["registers"],0)
    position = graph.entry
    state,head,ones = entry["state"],entry["head"],set(entry["ones"])
    events,checks,native = [],0,0
    for local in range(100_000_000):
        read_bit = int(head in ones)
        if read_bit and state in observed_names:
            while graph.rows[position][0].startswith(("_break.","_continue.")):
                position = graph.rows[position][1]
            operation,*targets = graph.rows[position]
            assert observed_names[state] == renamed(operation,mapping)
            actual,widths,end = bank(ones,capacity)
            expected = [sum(values[name] for name in groups[key]) for key in order]
            assert actual[:len(order)] == expected and not any(actual[len(order):])
            assert not any(cell >= end for cell in ones)
            checks += 1
            if operation == "beep":
                position = targets[0]
            else:
                kind,name = operand(operation)
                assert all(values[peer] == 0 for peer in groups[mapping[name]] if peer != name)
                values[name],outcome = value_step(kind,values[name])
                position = targets[outcome]
                native += kind in ("half","double","push1")
        write,move,target,event = rows[2*state+read_bit]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        state = target
        if event:
            events.append(entry["steps"]+local+1)
            if len(events) == 3:
                actual = dict(steps=entry["steps"]+local+1,state=state,head=head,ones=sorted(ones),events=events)
                assert actual == expected_final
                return dict(resumed_actual_checkpoint_sha256=jd(entry),physical_steps=local+1,
                            primitive_boundaries=checks,native_boundaries=native,
                            reserve_fields_checked=capacity-len(order),
                            complete_final_configuration_sha256=jd(actual),
                            scope="Reviewer Python sparse literal execution resumed from dual-engine actual blank entry; whole active bank, zero reserves, mapped ghost operations and zero-peer premises checked at every prepared primitive.")
    raise AssertionError("actual-boundary trace budget exhausted")


def physical(folder, source, out):
    programs = {}
    for name, expected in ENGINE_PINS.items():
        assert sha(PRIOR/name) == expected
        target = out / Path(name).stem
        compiler, standard = ("g++", "c++17") if name.endswith(".cpp") else ("gcc", "c11")
        subprocess.run([compiler,"-std="+standard,"-O2","-Wall","-Wextra","-Werror",str(PRIOR/name),"-o",str(target)], check=True)
        programs[name] = target
    def literal(name, limit=1_000_000_000, wanted=0, stop=-1, c=False):
        if c:
            args = [str(programs["literal_bitset.c"]), str(folder/name), str(limit), str(wanted), str(stop)]
        else:
            args = [str(programs["literal_review.cpp"]), str(folder/name), str(limit), str(stop), str(wanted)]
        result = json.loads(subprocess.check_output(args, text=True))
        if c:
            result["events"] = result.pop("beeps")
        return result
    bmap, emap, counts = row_maps(folder)
    names = read(folder/"names.json")
    prefix = literal("raw.tm", stop=names["binary.direct_bootstrap.entry"])
    assert prefix == literal("raw.tm", stop=names["binary.direct_bootstrap.entry"], c=True)
    assert prefix["steps"] == 2_133_492 and prefix["head"] == -2 and prefix["events"] == []
    assert prefix["ones"] == list(range(-3821,-2,2))+[-2,0,1,2,3]
    entry = literal("raw.tm", stop=names["main().0"])
    assert entry == literal("raw.tm", stop=names["main().0"], c=True)
    expected_ones = [-3822,-3821,3]+list(range(9,7642,4))
    assert entry["head"] == -3819 and entry["ones"] == expected_ones and entry["events"] == []
    for c in (False, True):
        assert literal("machine.tm", limit=entry["steps"], c=c) == {**entry,"state":mapped(bmap,entry["state"])}
    grammar = read(folder/"grammar.json")
    expected, stats = Graph(grammar).events(3)
    ghosts, ghost_stats = Graph(read(folder/"pre-coalescence-grammar.json")).events(3)
    sharing = read(folder/"bank-coalescence.json")
    sums = [{physical:sum(values[name] for name in members) for physical,members in sharing["groups"].items()} for values in ghosts]
    assert expected == sums
    originals = source_events(source,3)
    allocation = read(folder/"allocation.json")["mapping"]
    observations = []
    final_raw = None
    for number in range(1,4):
        observed = literal("machine.tm", wanted=number)
        assert observed == literal("machine.tm", wanted=number, c=True)
        capacity = read(folder/"binary-runtime.json")["zero_register_capacity"]
        values,widths,end = bank(observed["ones"],capacity)
        assert values[:len(grammar["registers"])] == [expected[number-1][register] for register in grammar["registers"]]
        assert not any(values[len(grammar["registers"]):])
        assert not any(position >= end for position in observed["ones"])
        assert ghosts[number-1][allocation["main.j"]] == originals[number-1]["j"]
        marked = literal("events.tm", limit=observed["steps"])
        assert marked == {**observed,"state":mapped(emap,observed["state"]),"events":[step-1 for step in observed["events"]]}
        observations.append(dict(candidate=originals[number-1]["j"],B_exit_step=observed["steps"],
                                 marked_step=observed["steps"]-1,whole_configuration_sha256=jd(observed),
                                 all_physical_values_match_ghost_sums=True,widths=widths[:len(grammar["registers"])],
                                 zero_reserve_fields=capacity-len(grammar["registers"])))
        if number == 3:
            final_raw = literal("raw.tm", wanted=3)
            assert final_raw == literal("raw.tm",wanted=3,c=True)
            assert {**final_raw,"state":mapped(bmap,final_raw["state"])} == observed
    boundaries = real_boundary_trace(folder,entry,final_raw)
    return dict(counts=counts,prefix_exit=dict(steps=prefix["steps"],head=prefix["head"],one_cells=len(prefix["ones"]),configuration_sha256=jd(prefix)),
                actual_blank_entry=dict(steps=entry["steps"],head=entry["head"],one_cells=len(entry["ones"]),zero_fields=1909,configuration_sha256=jd(entry)),
                events=observations,grammar=stats,ghost_grammar=ghost_stats,actual_primitive_boundaries=boundaries,
                injected_transducer_fixtures=transducer_fixtures(folder),
                engines=list(ENGINE_PINS),marked_engine="C++ plus all-row quotient and same-time full-configuration relation")


def check(folder, source, out):
    out.mkdir(parents=True, exist_ok=False)
    artifacts = {path.name:sha(path) for path in folder.iterdir() if path.is_file()}
    metadata = read(folder/"metadata.json")
    assert sha(source) == metadata["source_sha256"]
    result = dict(reviewer="internal-model-reviewer", source_sha256=sha(source), canonical_artifacts=artifacts,
                  storage=storage(folder), physical=physical(folder,source,out))
    assert result["physical"]["counts"]["raw"] == metadata["raw_states"]
    assert result["physical"]["counts"]["B_exit"] == metadata["states"]
    assert result["physical"]["counts"]["marked"] == metadata["event_states"]
    assert artifacts == {path.name:sha(path) for path in folder.iterdir() if path.is_file()}
    result["scope"] = "Independent exact all-row maps, native storage closure and fresh actual blank/three-event traces. Source compiler theorem, contextual rewrite algebra, generic kernels and direct transducer induction have separate written review. Finite traces do not decide eventual silence."
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--machine", type=Path, required=True)
    parser.add_argument("--source", type=Path, default=COMPACT/"source/certificate_popfirst_power.py")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--result", type=Path, required=True)
    args = parser.parse_args()
    result = check(args.machine,args.source,args.out)
    args.result.parent.mkdir(parents=True,exist_ok=True)
    args.result.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({"storage":result["storage"],"physical":result["physical"]},sort_keys=True,indent=2))
