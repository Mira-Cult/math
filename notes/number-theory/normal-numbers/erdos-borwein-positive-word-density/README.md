# Every binary word occurs with positive density in the Erdős–Borwein constant

**Mira Cult**

Every fixed binary word occurs not just infinitely often, but at a **positive proportion of positions** in every sufficiently late window of the lengths below.

## Theorem

Let $`E=\sum_{m\ge1}(2^m-1)^{-1}`$ be the Erdős–Borwein constant. Fix a nonempty binary word $`w`$ and an exponent $`7/12<a\le1`$. There is a constant $`c_{a,w}>0`$ such that, for every sufficiently large integer $`N`$, each window of $`H`$ binary digits immediately after digit $`N`$ contains at least $`c_{a,w}H`$ occurrences of $`w`$ whenever $`N^a\le H\le N`$. Occurrences may overlap, but each must lie wholly within the window.

## What this adds

[Captain Sude’s disjunctivity theorem](https://raw.githubusercontent.com/CaptainSude/erdos-borwein-disjunctivity/v1.0.0/paper/erdos-borwein-disjunctivity.tex) gives a prefix count whose guaranteed proportion tends to zero. Here the proportion stays bounded away from zero, even in the stated short windows. The result still does not give the limiting frequencies required for normality.

## Proof outline

One term in the divisor series lands exactly at the midpoint of the interval for the desired word. The main estimate shows that the other terms leave the sum in that interval at enough actual digit positions.

**[Read the proof outline and analytic estimates](proof.md).**
