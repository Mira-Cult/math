"""Literal complete-table accounting with native support shown separately.

The inherited independent checker verifies every physical row and quotient.
This additional disjoint partition distinguishes the native kernel, native
operand selector and native entries from the inherited engine. Shared classes
remain explicit instead of being counted twice.
"""
from collections import Counter
from pathlib import Path
import argparse
import importlib.util
import json

HERE = Path(__file__).resolve().parent
CONTINUATION = HERE.parents[1]
spec = importlib.util.spec_from_file_location('npconp_literal_cost_control', CONTINUATION/'cost_check.py')
control = importlib.util.module_from_spec(spec)
spec.loader.exec_module(control)


def category(name):
    if name.startswith('3.$native-half:'):
        return 'native half operation entries'
    if name.startswith('2h.native_half.select.') or name == '2h.native_half.prep':
        return 'native half selection and preparation'
    if name.startswith('2h.native_half.'):
        return 'native half kernel'
    return control.category(name)


def check(folder):
    folder = Path(folder)
    result = control.check(folder)
    names = json.loads((folder/'names.json').read_text())
    bmap = json.loads((folder/'quotient.json').read_text())
    emap = json.loads((folder/'event-quotient.json').read_text())['mapping']
    def lookup(mapping, key):
        return mapping[key] if isinstance(mapping, list) else mapping[str(key)]
    bclasses, eclasses = {}, {}
    for name, raw in names.items():
        parent = lookup(bmap, raw)
        event = lookup(emap, parent)
        bclasses.setdefault(parent, set()).add(category(name))
        eclasses.setdefault(event, set()).add(category(name))
    parts = lambda classes: dict(sorted(Counter(' + '.join(sorted(values))
                                                for values in classes.values()).items()))
    result['native_B_partition'] = parts(bclasses)
    result['native_event_partition'] = parts(eclasses)
    assert sum(result['native_B_partition'].values()) == result['B_exit_states']
    assert sum(result['native_event_partition'].values()) == result['event_states']
    result['native_partition_scope'] = 'each exact quotient class once; overlapping native/inherited roles explicitly combined'
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--directory', type=Path, default=HERE/'machines/selected')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    result = check(args.directory)
    if args.out:
        args.out.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    if args.check:
        assert result == json.loads(args.check.read_text())
    print(json.dumps(result, indent=2))
