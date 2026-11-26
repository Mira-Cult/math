# Maintaining “no adjacent aa” with unary existential updates

*Mira Cult*

## The problem

Start with a fixed finite row of empty slots. Each edit writes an `a` or a `b` into one slot, replacing whatever was there, or erases that slot. The word is what you read from left to right after skipping the empty slots. For example, the slots `a □ a` represent the word `aa`; writing `b` in the middle changes the answer from **no** to **yes**.

**Can we maintain a bit answering “Does the current word avoid `aa`?”** Use one program for every row size. Each edit must update the bit and all auxiliary relations simultaneously, using only the new letters, the old auxiliary state, the edited slot, and the order $<$. The auxiliary state can contain sets of individual slots and Boolean flags, but not relations on pairs of slots. An update formula may have existential quantifiers followed by a quantifier-free formula. Negated atoms are allowed; universal quantifiers, successor, and arithmetic are not needed. Initialization may use first-order logic.

**Yes.** The formulas below exhibit such a program, proving that the language of words with no adjacent `aa` belongs to $\mathrm{UDyn}\Sigma_1$. This refutes the explicit nonmembership claim about this language in [Conjecture 37 of Barloy, Tschirbs, Vortmeier and Zeume](https://arxiv.org/html/2601.18429v1#S6).

## The update formulas

Primes denote new auxiliary values; unprimed auxiliary values are old. The edit is at slot $i$. We give the formula for the answer first, then the formulas that maintain its inputs. Throughout, $\bot$ and $\top$ mean false and true, respectively.

### 1. Answer bit

Let $k$ be the number of adjacent `aa` pairs in the old word. The program represents $k$ by the prefix $T$ of the first $k$ slots, but stores only a unary relation $C$ and one bit $q$. The following is a quantifier-free abbreviation, not a separate stored relation:

$$
T(x)=(q\land C(x))\lor(\neg q\land\neg C(x)).
$$

Let $D_j$ be the quantifier-free test that this edit changes $k$ by $j$. Its formula is in the next subsection. Let $M_2,M_3$ be immutable unary marks for the second and third slots, empty when the indicated slot does not exist. **The formula for the new answer bit is**

$$
\boxed{
\mathrm{OK}'=\exists y\,\big[
(D_0\land\mathrm{OK})\lor
\big(\neg T(y)\land
((D_{-1}\land M_2(y))\lor(D_{-2}\land M_3(y)))\big)
\big].
}
$$

An increase returns false. With no change, the witness can be the edit slot $i$. After a decrease by $d\in\{1,2\}$, the new count is zero exactly when $k=d$. Since the old count is at least $d$, the test is that slot $d+1$ lies outside the old prefix. That slot exists: $d$ adjacent pairs require at least $d+1$ occupied slots.

### 2. Change in the count

Let $\ell=L(i)$ and $r=R(i)$ say that the nearest occupied slots strictly to the left and right of the edit carry `a`. A missing neighbor gives false. The next subsection gives the quantifier-free decoding of $L,R$.

For a symbol at $i$, let $A,B$ mean it is `a` and `b`, respectively, and $E=\neg A\land\neg B$ mean it is empty. The following tests give the number of pairs affected at $i$ before or after the edit:

| Number | Formula |
| --- | --- |
| 0 | $B\lor(A\land\neg\ell\land\neg r)\lor(E\land\neg(\ell\land r))$ |
| 1 | $(A\land((\ell\land\neg r)\lor(\neg\ell\land r)))\lor(E\land\ell\land r)$ |
| 2 | $A\land\ell\land r$ |

Call these tests $F_0,F_1,F_2$. Use the old letter at $i$ for $F_u^{\mathrm{old}}$ and the new one for $F_v^{\mathrm{new}}$. To read the old letter, store unary copies of the two input letter predicates and copy the new input into them at each edit. Then

$$
D_j=\bigvee_{\substack{u,v\in\{0,1,2\}\\v-u=j}}
(F_u^{\mathrm{old}}\land F_v^{\mathrm{new}}).
$$

When the slot is occupied by `a`, it can contribute one pair on each side; when occupied by `b`, it contributes none. When it is empty, the left and right neighbors form a single pair if both carry `a`. All other pairs are unchanged.

### 3. Nearest occupied letters

Store a unary relation $R_{\ast}$ and bit $p$, and decode the right-neighbor flag by $R(x)=(p\land R_{\ast}(x))\lor(\neg p\land\neg R_{\ast}(x))$. Store and decode the left-hand flag symmetrically. Write $n=R(x)$, $m=R(i)$, and set

$$
E_a(x,i)=\exists y\,(x<y\land y<i\land A_{\mathrm{new}}(y)),
\qquad
E_b(x,i)=\exists y\,(x<y\land y<i\land B_{\mathrm{new}}(y)).
$$

The interval excludes $i$, so either version of the input gives the same interval test. Here is the complete right-hand update; for the left-hand update reverse the order and use its own flag and polarity bit.

| Edit at $i$ | $p'$ | $R_{\ast}'(x)$ for $x\ge i$ | $R_{\ast}'(x)$ for $x<i$ |
| --- | --- | --- | --- |
| Write `a` | $\bot$ | $\neg n$ | $\neg n\land E_b(x,i)$ |
| Write `b` | $\top$ | $n$ | $n\land E_a(x,i)$ |
| Erase `a` | $\top$ | $n$ | $n\land(m\lor E_a(x,i))$ |
| Erase `b` | $\bot$ | $\neg n$ | $\neg n\land(\neg m\lor E_b(x,i))$ |
| Erase an empty slot | $\top$ | $n$ | $n$ |

For a write, an intervening occupied slot takes precedence over the edited letter. For example, after writing `a` at $i>x$, the new right-neighbor flag is false exactly when the first occupied slot in $(x,i)$ carries `b`. This is equivalent to $\neg n\land E_b(x,i)$. The table stores that negated flag so the interval test stays positive. On erasing `a`, a true old flag remains true if an `a` intervenes; otherwise it takes the value $R(i)$. A false old flag stays false. The “Erase `b`” row applies the same reasoning to the negated flag, which includes the case of a missing neighbor. The logical right-hand flag does not change for $x\ge i$.

### 4. Prefix counter

For $d=1,2$, use the following existential formulas. The distinctness condition is empty for $d=1$.

$$
\begin{aligned}
\mathrm{Down}_d(x)
&=\exists y_1\cdots y_d\,
  \left[\bigwedge_{h=1}^d(x<y_h\land T(y_h))
  \land\bigwedge_{h<j} y_h\ne y_j\right],\\
\mathrm{Up}_d(x)
&=\exists y_1\cdots y_d\,
  \left[\bigwedge_{h=1}^d(y_h<x\land\neg T(y_h))
  \land\bigwedge_{h<j} y_h\ne y_j\right].
\end{aligned}
$$

The updates are

$$
\begin{aligned}
q'&=D_{-2}\lor D_{-1}\lor D_0,\\
C'(x)&=(D_0\land T(x))\lor
(D_{-1}\land\mathrm{Down}_1(x))\lor(D_{-2}\land\mathrm{Down}_2(x))\\
&\qquad{}\lor(D_1\land\mathrm{Up}_1(x))\lor(D_2\land\mathrm{Up}_2(x)).
\end{aligned}
$$

If $x$ has rank $s$ in the order, then $\mathrm{Down}_d(x)$ holds exactly when $s\le k-d$; this stores the smaller prefix directly. The test $\mathrm{Up}_d(x)$ holds exactly when $s>k+d$; this stores the **complement** of the larger prefix. Switching which set is stored is what lets both updates use only existential tests. The ranks are used only in the proof, not in any formula.

### Initialization and correctness

Set the old-letter copies, the physical neighbor predicates and $C$ to empty; set the polarity bits and $\mathrm{OK}$ to true. The marks $M_2,M_3$ are first-order definable from the order and never change. For instance, mark $M_2(x)$ when exactly one slot is strictly below $x$. An empty domain has no updates and starts with the correct answer.

Every row condition in the neighbor table is quantifier-free. Each column-case and row-case can be combined by disjunction, and every quantified subformula occurs positively: decoded flags and their negations are themselves quantifier-free. To put the displayed rules in existential prenex form, rename witnesses and use the edit slot $i$ as a dummy witness in unused branches. The initialization and the invariants proved above give correctness by induction over all edit sequences.

## Other forbidden adjacent pairs

The same construction works for any fixed finite alphabet and any fixed set of forbidden ordered pairs. Store a nearest-neighbor flag for each letter; the neighbor table for that flag treats every other occupied letter as `b`. Count the forbidden pairs on the two sides of an occupied edit slot or across an empty one. The change is still in $\{-2,-1,0,1,2\}$, so the counter and answer formulas are unchanged. This does not cover arbitrary longer forbidden substrings.

## Reference and checker

Corentin Barloy, Felix Tschirbs, Nils Vortmeier and Thomas Zeume, *Algebraic Characterizations of Classes of Regular Languages in DynFO*, STACS 2026, [DOI 10.4230/LIPIcs.STACS.2026.9](https://doi.org/10.4230/LIPIcs.STACS.2026.9), §2.1 and §6. [Example 4](https://arxiv.org/html/2601.18429v1#S2.SS1) supplies the complemented-neighbor technique; the two-representation counter gives the answer for words that avoid `aa`. This addresses the concrete nonmembership claim, not a full characterization of the class or a result for positive existential updates.

Run [`python3 check.py`](check.py) for the exhaustive transition check on orders 0 through 7, including both old polarity bits. The proof covers all orders. No external referee review or formal verification is claimed.

Mira’s dots, using OpenAI’s GPT Astra models, assisted with developing and checking the proof.
