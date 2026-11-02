# A smaller lifted modulus for the exact-total targets

The preserved target source is
[cutoff_target_optimization.md](cutoff_target_optimization.md), frozen at
`4a117bf257a07f035af52fb6726dc0c9d52981b3`, SHA-256
`54fc5ff7446e4ff0c8abe3794dbd0fd4da807481cee7de172a1c989d86903e1c`.
Its statement and code remain unchanged. The refinement below is another
finite implication, not an analytic prime-count theorem or a square cutoff.

## TQ-S: the narrower modulus request

Use the same `y,D,ell,F,g,k,T,a_i` as TQ, but require `ell>=3` and
`F>=ell`. Retain TQ's exact size conditions


```math
D\le y/4,\qquad D\ge512F\ell^2,\qquad
 k\ge8\ell\{3F(4\ell+6)+7\}.                          \qquad\text{(TS1)}
```


Put the integer


```math
L=\left\lceil\frac{7(\ell+1)}{10}\right\rceil.          \qquad\text{(TS2)}
```


In place of TQ's first supply hypothesis, assume that every real interval
`I` inside `[y-D,y+D]` of length at least `D/2` contains at least


```math
\frac{|I|}{2\varphi(g)\log(2y)}                        \qquad\text{(TS3)}
```


primes in every reduced class modulo the even integer `g`. For the second
supply hypothesis it now suffices to have density `|I|/(hF)` for every
even multiple `h` of `g` with


```math
h\le gL.                                               \qquad\text{(TS4)}
```


The conclusion is exactly TQ's conclusion: primes `t_i` in the prescribed
classes modulo `g`, each within D of y, with repetitions permitted and
exact sum T. No input array entry is used or duplicated by this lemma.

### Proof of the sharper seed step

Since `g` is even, `phi(g)<=g/2`. Also `y<=2^ell` and `log2<7/10`,
so `log(2y)<7(ell+1)/10<=L`. The strong supply (TS3) is consequently
at least `|I|/(gL)`. For `ell>=3`, `7(ell+1)/10<=ell`, hence `L<=ell`.

Select a repeated original class a just as in TQ. In the seed interval
`[y-D/4,y+D/4]`, of length D/2, let `M_0` be the actual number of
primes in this class. Then


```math
M_0\ge\frac{D}{2gL}>1.                                \qquad\text{(TS5)}
```


The required strict inequality


```math
D>2gL(L+1)                                             \qquad\text{(TS6)}
```


follows from (TS1), `F>=ell`, `g<=16ell`, and `L<=ell`:


```math
D\ge512\ell^3>32\ell^2(\ell+1)\ge2gL(L+1).
```


The middle difference is `32ell^2(15ell-1)>0`. Thus no informal
"large enough" condition has been inserted.

Among consecutive seed primes one gap h is at most


```math
\frac{D}{2(M_0-1)}
 \le\frac{D}{2\{D/(2gL)-1\}}<g(L+1).                  \qquad\text{(TS7)}
```


The last inequality is exactly (TS6) after multiplying positive
denominators. The gap is a positive multiple of g. Both g and L are
integers, so the strict inequality in (TS7) proves **h<=gL**.
It is not enough merely to discard the `M_0-1` term; that would lose
the strict integer conclusion. The lower prime is greater than h, as in
TQ, so its residue modulo h is reduced.

### Rest of the exact-total proof

TQ Steps 2--6 use prime supplies only for this selected h and its reduced
classes. They therefore apply without change with the weaker uniform
request (TS4). In particular, `h<=gL<=16ell^2<128ell^2`, so the same
size condition D>=512Fell^2 still implies the initial `4Fh<=D` and
every later prefix/capacity condition. The fine grid, its extension to
2D, the `2P+5` wide pairs, two-coordinate congruence lifting, and greedy
discrepancy remain unchanged. This reapplies the proof to its actual
selected modulus; it does not invoke TQ's larger literal weak-supply
premise without establishing it. This proves TQ-S.

Every requested analytic interval still has length at least D/2. Binning
the already supplied central set does not invoke another prime theorem.
All rounded quantities are treated pointwise; there is no derivative
argument across a ceiling change.

## Coupling to the sharper input-pool seed

If a separately proved entry-seed theorem gives `g<=E<=ell`, then


```math
h\le E L\le\ell L\le\frac34\ell^2\quad(\ell\ge34),     \qquad\text{(TS8)}
```


because `L<=7ell/10+17/10`. The right inequality follows from
`ell/20>=17/10`. This already improves the old request `128ell^2`
by a factor exceeding 170, when the smaller initial gap is available.
It is a smaller sufficient analytic modulus range, not a restriction on
the theorem's allowed array orders.

If the composition also proves `E<7ell/10`, then


```math
h<\frac{49}{100}\ell^2+\frac{119}{100}\ell
 \le\frac12\ell^2\qquad(\ell\ge119).                  \qquad\text{(TS9)}
```


The final comparison is just `ell(ell-119)>=0`. The source of
`E<7ell/10` and its domain must be established by the composition; it is
not an assumption about independently varying E and ell. The resulting
uniform weak-analytic request can use every even q<=ell^2/2, which includes
the actual selected h. The present target proof does not decide the best
analytic scale at which that request is available.

The target construction itself permits any D satisfying (TS1). In
particular a proposed change from `D=y/ell^4` to `D=y/ell^3` changes no
finite target step. The complete square theorem must separately recheck
the target size, required analytic length D/2, and controller displacement.

## Verification and dependency boundary

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).
The program binds the exact preserved TQ proof and code, checks the
integer-gap and ceiling envelopes, exercises finite examples of the
strict predecessor argument, and rejects malformed input/source bindings.
It does not certify the prime supplies (TS3)--(TS4), the sharper input-pool
seed theorem, or the E/ell coupling. Those remain separately proved and
reviewed dependencies of any final square cutoff.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
