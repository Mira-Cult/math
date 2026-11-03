#!/usr/bin/env python3
"""Seeded finite search for the exactly prescribed trace-energy pools.

The exact certificate checker is separate. Exhausting a search budget does
not establish an obstruction. This producer neither modifies nor imports the
frozen quartic producer.
"""
import argparse
import json
import math
import random
from pathlib import Path
from energy_cyclotomic import EnergyField, lines, certificate


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--m', type=int, choices=(7, 9, 15, 16), required=True)
    p.add_argument('--n', type=int, required=True)
    p.add_argument('--D', type=int, choices=(2, 3), default=2)
    p.add_argument('--seed', type=int, default=20261103)
    p.add_argument('--steps', type=int, default=100000)
    p.add_argument('--restarts', type=int, default=20)
    p.add_argument('--energy-bound', type=int)
    p.add_argument('--pool-cache')
    p.add_argument('--output', required=True)
    args = p.parse_args()
    if args.m in (5, 8, 12):
        p.error('the frozen quartic fields use their existing balanced-log producer')
    f = EnergyField(args.m); count = args.n**args.D
    cache = Path(args.pool_cache) if args.pool_cache else None
    cached = json.loads(cache.read_text()) if cache and cache.exists() else None
    if cached and cached['conductor'] == args.m and len(cached['pool']) >= count:
        pool = [tuple(x) for x in cached['pool'][:count]]
        completeness = cached['pool_completeness']
        cutoff = f.norm(pool[-1])
        completeness['norm_cutoff'] = cutoff
        completeness['all_through_cutoff'] = [a for a in completeness['all_through_cutoff'] if f.norm(tuple(a)) <= cutoff]
    else:
        pool, completeness = f.pool(count, args.energy_bound,
            progress=lambda x:print(json.dumps(x),flush=True))
        if cache:
            cache.write_text(json.dumps({'conductor':args.m,'pool':pool,'pool_completeness':completeness})+'\n')
    required = lines(args.n,args.D)
    incidence = [set() for _ in pool]
    for j, line in enumerate(required):
        for i in line:
            incidence[i].add(j)
    rng = random.Random(args.seed); best = len(required)+1
    for restart in range(args.restarts):
        a = pool[:]; rng.shuffle(a)
        sums = [tuple(sum(a[i][k] for i in line) for k in range(f.r)) for line in required]
        bad = [f.prime_record(s) is None for s in sums]; score = sum(bad)
        for step in range(args.steps+1):
            if score < best:
                best = score
            if not score:
                metadata = {'method':'seeded-whole-element-swap-annealing','seed':args.seed,
                    'steps_per_restart':args.steps,'restarts_budget':args.restarts,
                    'restart':restart,'successful_step':step}
                data = certificate(f,args.n,args.D,pool,completeness,a,metadata)
                Path(args.output).write_text(json.dumps(data,indent=2)+'\n')
                print(json.dumps({'status':'found','output':args.output,'lines':len(required),'metadata':metadata}),flush=True)
                return 0
            failures = [j for j, b in enumerate(bad) if b]
            i = rng.choice(required[rng.choice(failures)]); j = rng.randrange(count)
            if i == j:
                continue
            delta = tuple(a[j][k]-a[i][k] for k in range(f.r))
            affected = incidence[i]^incidence[j]
            changed = {k:tuple(sums[k][u]+(delta[u] if k in incidence[i] else -delta[u]) for u in range(f.r)) for k in affected}
            new_bad = {k:f.prime_record(s) is None for k,s in changed.items()}
            difference = sum(new_bad[k]-bad[k] for k in affected)
            temperature = 0.10+0.70*(1-(step % 5000)/5000)
            if difference <= 0 or rng.random() < math.exp(-difference/temperature):
                a[i], a[j] = a[j], a[i]
                for k,s in changed.items():
                    sums[k],bad[k] = s,new_bad[k]
                score += difference
        print(json.dumps({'m':args.m,'n':args.n,'D':args.D,'restart':restart,'best_bad':best}),flush=True)
    print(json.dumps({'status':'budget-exhausted-not-an-obstruction','best_bad':best}))
    return 1


if __name__ == '__main__':
    raise SystemExit(main())
