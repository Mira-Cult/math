"""Reassociate only closed sequential control, then share repeated word pairs.

This is a separate experiment over the pinned tree grammar.  No source-language
semantics, primitive operations, or nonclosed control pairs are changed.
"""
from collections import Counter
from functools import lru_cache
import random


def analyze(nodes, *, commute=False):
    absent = -10**9

    @lru_cache(None)
    def demand(value):
        if isinstance(value, str):
            if value.startswith('_break.'):
                return int(value.split('.')[1]), absent
            if value.startswith('_continue.'):
                return absent, int(value.split('.')[1])
            if value.endswith('.decnz'):
                return 1, absent
            if value == 'beep' or value.endswith('.inc'):
                return 0, absent
            raise ValueError('unknown primitive: ' + value)
        children = nodes[value]
        if len(children) != 2:
            raise ValueError('binary grammar required')
        a, b = demand(children[0]), demand(children[1])
        return max(a[0]-1,b[0]), max(a[1],b[1]-1)

    @lru_cache(None)
    def effects(value):
        if value[0] == 'op':
            op=value[1]
            if op == 'beep':return frozenset(),True
            if op.startswith('3.'):
                return frozenset([op[2:].rsplit('.',1)[0]]),False
            return frozenset(),False
        children=value[1] if value[0]=='word' else value[1:]
        seen=frozenset();event=False
        for child in children:
            regs,emits=effects(child);seen|=regs;event|=emits
        return seen,event

    def commute_word(xs):
        if not commute:return xs
        facts=[effects(x) for x in xs]
        pending=set(range(len(xs)));out=[]
        while pending:
            ready=[i for i in pending if not any(
                j<i and (facts[i][1] or facts[j][1] or facts[i][0]&facts[j][0])
                for j in pending)]
            i=min(ready,key=lambda j:(repr(xs[j]),j))
            out.append(xs[i]);pending.remove(i)
        return tuple(out)

    @lru_cache(None)
    def normal(value):
        if isinstance(value, str):
            return ('op', value)
        left, right = nodes[value]
        a, b = normal(left), normal(right)
        if max(demand(left)) <= 0 and max(demand(right)) <= 0:
            aa = a[1] if a[0] == 'word' else (a,)
            bb = b[1] if b[0] == 'word' else (b,)
            return ('word', commute_word(aa + bb))
        return ('pair', a, b)

    return demand, normal


def refactor(builder, *, seed=0, scoring='gain', rounds=10000, commute=False):
    original = tuple(tuple(s.seq) for s in builder.sequences)
    root = builder.find_seq('main().0')
    old_reachable_count = len(list(builder.reachable()))
    demand, normal = analyze(original,commute=commute)
    normalized = normal(root)
    # Structural values are finite DAG expressions.  A word is only formed
    # when each constituent has no escaping conditional/loop continuation.
    words = {}
    def collect(value):
        if value[0] == 'word':
            if value in words:
                return
            words[value] = value[1]
            for child in value[1]:
                collect(child)
        elif value[0] == 'pair':
            collect(value[1]); collect(value[2])
    collect(normalized)
    streams = list(words.values())
    keys = list(words)
    rules = []
    rng = random.Random(seed)
    decisions = []
    for _ in range(rounds):
        counts = Counter()
        for stream in streams:
            # Nonoverlapping occurrences are the only replacements charged.
            seen = set(zip(stream, stream[1:]))
            for pair in seen:
                j = 0
                while j+1 < len(stream):
                    if stream[j:j+2] == pair:
                        counts[pair] += 1; j += 2
                    else:
                        j += 1
        viable = [pair for pair, n in counts.items() if n >= 2]
        if not viable:
            break
        def score(pair):
            n = counts[pair]
            if scoring == 'gain':
                return n
            if scoring == 'random':
                return n + rng.random()*3
            if scoring == 'prefer-right':
                return n + sum(stream[-2:] == pair for stream in streams)*0.5
            raise ValueError(scoring)
        # Stable first occurrence resolves ties; never depend on hash order.
        order = {pair:i for i,pair in enumerate(dict.fromkeys(
            pair for stream in streams for pair in zip(stream,stream[1:])))}
        viable.sort(key=lambda pair: order[pair])
        pair = max(viable, key=score)
        token = ('rule', len(rules))
        rules.append(pair)
        decisions.append({'uses': counts[pair]})
        for i,stream in enumerate(streams):
            out=[]; j=0
            while j < len(stream):
                if stream[j:j+2] == pair:
                    out.append(token); j+=2
                else:
                    out.append(stream[j]); j+=1
            streams[i]=tuple(out)

    words = dict(zip(keys, streams))
    from TMBuilder import Sequence
    nodes=[]; lookup={}; memo={}
    def pair_node(a,b):
        pair=(a,b)
        if pair not in lookup:
            lookup[pair]=len(nodes);nodes.append(pair)
        return lookup[pair]
    def emit_word(xs):
        value=emit(xs[-1])
        for child in reversed(xs[:-1]):
            value=pair_node(emit(child),value)
        return value
    def emit(value):
        if value in memo:return memo[value]
        kind=value[0]
        if kind=='op':out=value[1]
        elif kind=='pair':out=pair_node(emit(value[1]),emit(value[2]))
        elif kind=='word':out=emit_word(words[value])
        elif kind=='rule':out=pair_node(emit(rules[value[1]][0]),emit(rules[value[1]][1]))
        else:raise ValueError(kind)
        memo[value]=out;return out
    new_root=emit(normalized)
    if not isinstance(new_root,int):raise ValueError('nontrivial root required')
    # A complete check compares independent reassociation normal forms.
    _, target_normal = analyze(tuple(nodes),commute=commute)
    if target_normal(new_root) != normalized:
        raise ValueError('closed-sequence expansion changed')
    builder.sequences=[Sequence(pair) for pair in nodes]
    builder.sequence_lookup={pair:i for i,pair in enumerate(nodes)}
    for i,s in enumerate(builder.sequences):
        s.name='main().0' if i==new_root else f'closed_{i}.0'
    builder.closed_sequence_certificate={
        'seed':seed,'scoring':scoring,'rounds':rounds,'commute':commute,
        'old_reachable_nodes':old_reachable_count,
        'new_nodes':len(nodes),'shared_pairs':len(rules),
        'closed_words':len(words),'decisions':decisions,
        'equivalence':('closed independent-register commutations; events and returned registers preserved'
                       if commute else 'same closed-word normal form; primitive trace and all registers preserved'),
    }
    return builder.closed_sequence_certificate
