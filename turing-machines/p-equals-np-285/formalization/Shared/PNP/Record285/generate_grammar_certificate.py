#!/usr/bin/env python3
"""Generate control-grammar data and exact-serialization certificates.

The JSON source and machine table are frozen inputs. Lean checks the generated
serialization and table certificates; this generator is not trusted.
"""
from collections import deque
from hashlib import sha256
from pathlib import Path
import json
import re
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("--check", action="store_true")
args = parser.parse_args()

def emit(path, content):
    if args.check:
        if path.read_text() != content:
            raise ValueError(f"generated source differs: {path.name}")
    else:
        path.write_text(content)


HERE = Path(__file__).resolve().parent
RAW = (HERE / "producer-grammar.json").read_bytes()
if sha256(RAW).hexdigest() != "b89fa51a9c90db473655aa94b74475104b4bdd3c7b73d13791a227d4a2599133":
    raise ValueError("unexpected source grammar bytes")
text = RAW.decode("ascii")
grammar = json.loads(text)
if json.dumps(grammar, indent=2) + "\n" != text or grammar["root"] != 162:
    raise ValueError("unexpected grammar serialization or root")
nodes = grammar["nodes"]
if len(nodes) != 163 or grammar["registers"] != [f"$coalesced.{i}" for i in range(15)]:
    raise ValueError("unexpected grammar dimensions")

rows = {}
for line in (HERE / "events.tm").read_text().splitlines():
    if line.startswith("#") or not line.strip():
        continue
    q, b, w, move, nxt, flag = line.split()
    rows[(int(q), int(b))] = (int(w), move, int(nxt), int(flag))
if len(rows) != 570:
    raise ValueError("unexpected table size")

state_map = {162: 284}
queue = deque([162])
while queue:
    node = queue.popleft()
    for b, edge in enumerate(nodes[node]):
        if "node" not in edge:
            continue
        w, move, nxt, flag = rows[state_map[node], b]
        if (w, move, flag) != (b, "R", 0):
            raise ValueError("non-preserving node edge")
        other = edge["node"]
        if other in state_map and state_map[other] != nxt:
            raise ValueError("nonfunctional node mapping")
        if other not in state_map:
            state_map[other] = nxt
            queue.append(other)
if set(state_map) != set(range(len(nodes))):
    raise ValueError("unreachable grammar node")


def edge(e):
    if set(e) == {"node"}:
        return f".node {e['node']}"
    name = e["op"]
    if name == "beep":
        return ".beep"
    if m := re.fullmatch(r"3\.\$coalesced\.(\d+)\.(inc|decnz)", name):
        return f".{ 'inc' if m[2] == 'inc' else 'dec' } {m[1]}"
    if m := re.fullmatch(r"3\.\$native-half:\$coalesced\.(\d+)\.decnz", name):
        return f".half {m[1]}"
    if m := re.fullmatch(r"_(break|continue)\.(\d+)", name):
        return f".{ 'brk' if m[1] == 'break' else 'cont' } {m[2]}"
    raise ValueError(f"unrecognized grammar edge: {e}")


def chars(s):
    def char(c):
        if c == "\n": return "'\\n'"
        if c == "'": return "'\\\''"
        if c == "\\": return "'\\\\'"
        if not 32 <= ord(c) <= 126: raise ValueError("non-ASCII character")
        return "'" + c + "'"
    return ",".join(map(char, s))


def node_text(node, last):
    rendered = "\n".join("    " + line for line in json.dumps(node, indent=2).splitlines())
    return rendered + ("\n" if last else ",\n")

node_texts = [node_text(n, i == len(nodes)-1) for i, n in enumerate(nodes)]
header = '{\n  "nodes": [\n'
suffix = text[len(header)+sum(map(len,node_texts)):]
if header + "".join(node_texts) + suffix != text:
    raise ValueError("serialization does not reassemble")
chunks = [list(range(i, min(i+4, len(nodes)))) for i in range(0, len(nodes), 4)]
base = ["import Shared.PNP.Record285.GrammarCore", "", "namespace Shared.PNP.Record285.Grammar", ""]
for c, idxs in enumerate(chunks):
    entries = []
    for i in idxs:
        a, b = nodes[i]
        entries.append(f"(({edge(a)}, {edge(b)}), {'true' if i == len(nodes)-1 else 'false'})")
    base.append(f"def entries{c} : List Entry := [" + ", ".join(entries) + "]")
base.append(f"def entriesFrom{len(chunks)} : List Entry := []")
for c in reversed(range(len(chunks))):
    base.append(f"def entriesFrom{c} : List Entry := entries{c} ++ entriesFrom{c+1}")
base += ["def entries : List Entry := entriesFrom0", "def nodes : Array Node := (entries.map Prod.fst).toArray",
         "def stateMap : Array Nat := #[" + ", ".join(str(state_map[i]) for i in range(len(nodes))) + "]",
         "", "end Shared.PNP.Record285.Grammar", ""]
emit(HERE / "GrammarData.lean", "\n".join(base))

fast_nodes = [f"({edge(n[0])}, {edge(n[1])})" for n in nodes]
fast = ["import Shared.PNP.Record285.GrammarData", "", "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 0", "namespace Shared.PNP.Record285.Grammar", "",
        "def fastNodes : Array Node := #[" + ", ".join(fast_nodes) + "]",
        "theorem nodes_fast : nodes = fastNodes := by rfl", "",
        "end Shared.PNP.Record285.Grammar", ""]
emit(HERE / "GrammarFastData.lean", "\n".join(fast))

out = ["import Shared.PNP.Record285.GrammarData", "", "set_option maxRecDepth 131072",
       "set_option maxHeartbeats 0", "", "namespace Shared.PNP.Record285.Grammar", "",
       "def literalChars : List Char := [" + chars(text) + "]",
       "theorem literal_chars : literal = String.ofList literalChars := by rfl", "",
       "def headerChars : List Char := [" + chars(header) + "]",
       "def suffixChars : List Char := [" + chars(suffix) + "]", ""]
for c, idxs in enumerate(chunks):
    block = "".join(node_texts[i] for i in idxs)
    out += [f"def chars{c} : List Char := [" + chars(block) + "]",
            f"theorem chars_ok{c} : renderEntries entries{c} = chars{c} := by decide", ""]
out += [f"def charsFrom{len(chunks)} : List Char := []",
        f"theorem rendered{len(chunks)} : renderEntries entriesFrom{len(chunks)} = charsFrom{len(chunks)} := rfl", ""]
for c in reversed(range(len(chunks))):
    out += [f"def charsFrom{c} : List Char := chars{c} ++ charsFrom{c+1}",
            f"theorem rendered{c} : renderEntries entriesFrom{c} = charsFrom{c} := by",
            f"  change renderEntries (entries{c} ++ entriesFrom{c+1}) = chars{c} ++ charsFrom{c+1}",
            f"  rw [renderEntries_append, chars_ok{c}, rendered{c+1}]", ""]
out += ["theorem chars_concat : literalChars = headerChars ++ charsFrom0 ++ suffixChars := by rfl", "",
        "/-- Exact byte-for-byte grammar text equals the serialization of the typed data. -/",
        "theorem literal_serialization : literal = String.ofList (headerChars ++ renderEntries entries ++ suffixChars) := by",
        "  rw [literal_chars, chars_concat]", "  change _ = String.ofList (headerChars ++ renderEntries entriesFrom0 ++ suffixChars)",
        "  rw [rendered0]", "", "end Shared.PNP.Record285.Grammar", ""]
emit(HERE / "GrammarTextCertificate.lean", "\n".join(out))
print(f"{len(nodes)} nodes, {len(chunks)} text segments; generated table-state map")
