# Theories K: a formal substitution catalogue

**Version:** 2026-10-23, definitions draft.  
**Purpose:** precise schemas, not a poster, state-count claim, or proof certificate.

Every row below defines a first-order theory. The non-original K rows are research presentations. Their asserted strength reductions must not be confused with the published calibrations of the conventional principles they are designed to interpret. In particular, an upstream proof of ordinary K/ZFC equiconsistency is not a proof of any modified K theory. The PA and member-request rows retain the mathematical arguments and outstanding obligations from the earlier research. No new full equivalence has been formally verified in this packet.

## 1. Syntax and the master schema

Use classical first-order logic with equality in the language $`L=\{E\}`$. Write $`x\in y`$ for $`E(x,y)`$. The universe is nonempty. Formula metavariables are not quantified inside the theory.

For each L-formula $`\varphi(y,p,q)`$, with arbitrary finite parameter tuple q, all displayed bound variables are chosen fresh and all substitutions are capture-avoiding. Define

```math
\begin{aligned}
P_\varphi(p)&:=\exists y\,\varphi(y,p),\\
W_0(p,C)&:=P_\varphi(p)\to\exists y\,(y\in C\land\varphi(y,p)).
\end{aligned}
```

A seed template $`S_\varphi(x,a)`$, an eligibility template $`R(p,a,C)`$, a response template $`W_\varphi(p,C)`$, and a bound condition $`B(C)`$ specify the theory consisting of the universal closures of

```math
\boxed{\begin{aligned}
\forall a\,\forall x\,\exists C\bigl[&
(S_\varphi(x,a)\to x\in C)\\
&\land\forall u\,(u\in C\to\exists p\,\varphi(u,p))\\
&\land\forall p\,(R(p,a,C)\to W_\varphi(p,C))\\
&\land B(C)\bigr].
\end{aligned}}\tag{K*}
```

Universal closure binds $`\varphi`$'s additional parameters and all extra row parameters (such as t and a signature $`\sigma`$) **outside** a,x,C. C and the other freshly bound names do not occur free in the matrix $`\varphi`$. In the scoped row, U is an explicitly declared individual constant and is not universally closed.

The support, request, and bound clauses are required even when the seed is false. Eligibility is outside the quantified support clause. This is essential for fixed-input collection when C is empty.

Abbreviations:

```math
\begin{aligned}
p\subseteq u&:=\forall z\,(z\in p\to z\in u),\\
R_a(p,a,C)&:=p\in a,\\
R_\in(p,a,C)&:=\exists u\,(u\in C\land p\in u),\\
R_\subseteq(p,a,C)&:=\exists u\,(u\in C\land p\subseteq u).
\end{aligned}
```

## 2. Substitutions and consistency calibrations

In the table, $`S=a`$ means $`S_\varphi(x,a)=\varphi(x,a)`$; $`S=x`$ means $`\varphi(x,x)`$. Every W and B is defined below. The scope row uses the explicit syntactic operator (L), not an undefined predicate called 'inaccessible'.

### Schema substitutions

| Theory | Seed | Eligibility | Response | Bound |
| --- | --- | --- | --- | --- |
| $`K_{\mathrm{fin}}`$ | $`x`$ | $`R_a`$ | $`W_0`$ | $`\mathrm{true}`$ |
| $`K_{\mathrm{mem}}`$ | $`a`$ | $`R_{\in}`$ | $`W_0`$ | $`\mathrm{true}`$ |
| $`K`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_0`$ | $`\mathrm{true}`$ |
| $`K_{\mathrm{Bor}}^{\mathrm{wo}}`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_{\mathrm{game}}^{\omega,\mathrm{Bor}}`$ | $`\mathrm{WO}_t`$ |
| $`K_{\mathrm{OD}}^{\mathrm{wo}}`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_{\mathrm{game}}^{\omega,\mathrm{OD}}`$ | $`\mathrm{WO}_t`$ |
| $`K_{\mathrm{OD}(\mathbb R)}^{\mathrm{wo}}`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_{\mathrm{game}}^{\omega,\mathrm{OD}(\mathbb R)}`$ | $`\mathrm{WO}_t`$ |
| $`K_{\mathrm{AD}}`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_{\mathrm{game}}^{\omega,\mathrm{All}}`$ | $`\mathrm{true}`$ |
| $`K_{\mathrm{AD}_{\mathbb R}}`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_{\mathrm{game}}^{\omega^\omega,\mathrm{All}}`$ | $`\mathrm{true}`$ |
| $`K_{\mathrm{product}}`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_{\mathrm{struct}}^{\mathrm{product}}`$ | $`\mathrm{true}`$ |
| $`K_{\mathrm{weak\text{-}product}}`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_{\mathrm{struct}}^{\mathrm{weak\text{-}product}}`$ | $`\mathrm{true}`$ |
| $`K_{\mathrm{elementary}}`$ | $`a`$ | $`R_{\subseteq}`$ | $`W_{\mathrm{struct}}^{\mathrm{elementary}}`$ | $`\mathrm{true}`$ |
| $`K_{\mathrm{scope}}`$ | — | — | — | — |

### Claimed or target consistency calibrations

| Theory | Calibration and status |
| --- | --- |
| $`K_{\mathrm{fin}}`$ | PA (research reduction) |
| $`K_{\mathrm{mem}}`$ | Full second-order arithmetic $`Z_2`$ (research reduction) |
| $`K`$ | ZFC (upstream formal result) |
| $`K_{\mathrm{Bor}}^{\mathrm{wo}}`$ | ZFC; Borel-determinacy calibration/control |
| $`K_{\mathrm{OD}}^{\mathrm{wo}}`$ | ZFC + one Woodin (research K translation) |
| $`K_{\mathrm{OD}(\mathbb R)}^{\mathrm{wo}}`$ | ZFC + $`\omega`$-many Woodins (research K translation) |
| $`K_{\mathrm{AD}}`$ | ZF + AD (research K translation) |
| $`K_{\mathrm{AD}_{\mathbb R}}`$ | ZF + $`\mathrm{AD}_{\mathbb R}`$, no extra DC claim (research K translation) |
| $`K_{\mathrm{product}}`$ | ZFC + 'Ord is Woodin' (research K translation) |
| $`K_{\mathrm{weak\text{-}product}}`$ | ZFC + 'Ord is essentially subtle' (research K translation) |
| $`K_{\mathrm{elementary}}`$ | ZFC + Vopenka's principle (research K translation) |
| $`K_{\mathrm{scope}}`$ | Apply (L); proposed ZFC + one inaccessible calibration |

The Borel row is intentionally a control: twelve presentations do not mean twelve distinct consistency strengths. No measurable-cardinal, n-inaccessible, or inaccessible-limit row is asserted merely by a prose label. Those require their own precise substitutions and reductions.

## 3. The fixed interpretation dictionary

Advanced rows must not treat raw E as extensional membership. Here is a definite finite first-order dictionary; it follows the tagged bisimulation construction of the pinned K source. All quantifiers in the following definitions are raw unless explicitly relativized.

```math
\begin{aligned}
\mathrm{Empty}(t)&:=\forall z\,\neg E(z,t),\\
D_t(x)&:=E(t,x),\\
\mathrm{Sing}(x,s)&:=\forall z(E(z,s)\leftrightarrow z=x),\\
\mathrm{Pair}(x,y,s)&:=\forall z(E(z,s)\leftrightarrow(z=x\lor z=y)),\\[4pt]
\mathrm{OP}(x,y,c)&:=
(\exists s(E(s,c)\land\mathrm{Sing}(x,s)))\\
&\quad\land(\exists s(E(s,c)\land\mathrm{Pair}(x,y,s)))\\
&\quad\land\forall s(E(s,c)\to
(\mathrm{Sing}(x,s)\lor\mathrm{Pair}(x,y,s))),\\[4pt]
\mathrm{Edge}(r,x,y)&:=\exists c(E(c,r)\land\mathrm{OP}(x,y,c)).
\end{aligned}
```

The ordered-pair code allows multiple raw singleton/pair representatives, as the pinned construction does; a code still determines its endpoints. Define

```math
\begin{aligned}
\mathrm{Bis}_t(r):={}&D_t(r)\\
&\land\forall x\forall y\bigl(\mathrm{Edge}(r,x,y)\to\bigl[D_t(x)\land D_t(y)\\
&\quad\land\forall u((D_t(u)\land E(u,x))\\
&\qquad\to\exists v(D_t(v)\land E(v,y)\land\mathrm{Edge}(r,u,v)))\\
&\quad\land\forall v((D_t(v)\land E(v,y))\\
&\qquad\to\exists u(D_t(u)\land E(u,x)\land\mathrm{Edge}(r,u,v)))\bigr]\bigr),\\[4pt]
x\sim_t y&:=\exists r(\mathrm{Bis}_t(r)\land\mathrm{Edge}(r,x,y)),\\
x\mathrel{e_t}y&:=\exists z(D_t(z)\land E(z,y)\land x\sim_t z).
\end{aligned}
```

The syntactic translation $`Q_t`$ replaces equality by $`\sim_t`$, membership by $`e_t`$, and every quantifier by its restriction to $`D_t`$. It commutes with propositional connectives. It is a translation of each actual formula, not an assumed truth predicate for the universe. In models of ordinary K and $`\mathrm{Empty}(t)`$, the resulting quotient is a model of ZF without Foundation.

For the well-founded core use the ordinary set-language formula $`\mathrm{RankSet}(x)`$:

```math
\begin{aligned}
\exists\alpha\,\exists h\,\bigl[&
\mathrm{Ord}(\alpha)\land\mathrm{Fun}(h)\\
&\land\mathrm{dom}(h)=\alpha+1
\land h(0)=\varnothing\\
&\land\forall\beta<\alpha\;h(\beta+1)=\mathcal P(h(\beta))\\
&\land\forall\lambda\le\alpha\;\bigl(\mathrm{Lim}(\lambda)
\to h(\lambda)=\bigcup_{\beta<\lambda}h(\beta)\bigr)\\
&\land x\in h(\alpha)\bigr].
\end{aligned}
```

Ord means a transitive set well-ordered by membership; Fun, domains, power sets, indexed unions and function values have their usual set-theoretic graph definitions. They do not quantify over proper classes. Let

```math
J_t(x):=D_t(x)\land\mathrm{RankSet}^{Q_t}(x).
```

The translation $`J_t`$ replaces atomic formulas as $`Q_t`$ does and restricts quantifiers to $`J_t`$. This is the fixed interpreted ZF universe used in the game and structure rows. $`q_t(y)`$, or $`\bar y`$, means the interpreted object represented by y; it is not a new primitive function. Equality of interpreted objects is $`\sim_t`$.

Every displayed image set has an explicit membership definition. For example:

```math
\begin{aligned}
\mathrm{Img}_t(C,F):={}&J_t(F)\land\forall z\bigl(J_t(z)\to\\
&\quad[z\,e_t\,F\leftrightarrow
\exists y(E(y,C)\land J_t(y)\land y\sim_t z)]\bigr).
\end{aligned}
```

'$`F=\mathrm{Img}(C)`$' means this formula with an existentially bound F, not a claim that an unbounded class automatically forms a set. Filtered images add their filter to the right-hand side.

Set-coded functions, sequences, products, homomorphisms, and satisfaction for **set-sized** structures are standard definitional abbreviations in the $`J_t`$ language. No global truth predicate, second-order relation quantifier, or external well-foundedness predicate is allowed.

## 4. Wellorderable bounds

Let $`\mathrm{WellOrd}(A,r)`$ say: r is a strict linear ordering of A and

```math
\forall B\,[\varnothing\ne B\subseteq A\to
\exists b\in B\;\forall c\in B\;\neg(c\,r\,b)].
```

Define the raw bound condition

```math
\begin{aligned}
\mathrm{WO}_t(C):={}&\mathrm{Empty}(t)\to\\
&\exists F\,\bigl[\mathrm{Img}_t(C,F)\land
(\exists r\,\mathrm{WellOrd}(F,r))^{J_t}\bigr].
\end{aligned}
```

The wellordering is an internally coded set relation. This condition does not identify raw equality with quotient equality.

## 5. Game responses

All games have length $`\omega`$, with moves in a nonempty set X and Player I moving at even positions. In $`J_t`$ let

```math
\begin{aligned}
\mathrm{II}_X&:=\{\tau:X^{<\omega}_{\rm odd}\to X\},\\
r\models\tau&:=\forall n\in\omega\;r(2n+1)=\tau(r\upharpoonright(2n+1)),\\
\mathrm{Ans}_X(A)&:=\forall\tau\in\mathrm{II}_X\;\exists r\in A\;(r\models\tau),\\
\mathrm{Coh}_X(S)&:=\forall r,s\in S\;\forall n\in\omega\;\\
&\quad(r\upharpoonright2n=s\upharpoonright2n\to r(2n)=s(2n)).
\end{aligned}
```

Sequences are function graphs; finite domains are natural numbers. The two choices of X are $`\omega`$ and $`\omega^\omega`$. Reals are represented as Baire-space sequences for this catalogue.

For a raw matrix $`\varphi`$ and raw p, $`\mathrm{Pay}_X(\varphi,p,A)`$ means

```math
\begin{aligned}
J_t(A)\land\forall r\in J_t\bigl[r\,e_t\,A\leftrightarrow{}&
\bigl((r\in X^\omega)^{J_t}\\
&\land\exists y(J_t(y)\land y\sim_t r\land\varphi(y,p))\bigr)\bigr].
\end{aligned}
```

For a raw D, $`\mathrm{Plays}_X(D,S)`$ is the analogous formula with $`\exists y\,(y\in D\land J_t(y)\land y\sim_t r)`$ instead of $`\varphi(y,p)`$. Thus A describes the whole projected payoff and S describes the projected plays in D. If no set A has the payoff profile, the game constraint is inactive.

A raw witness packet is

```math
\begin{aligned}
\mathrm{Pkt}_\varphi(D,p,C):={}&
(\exists y\,y\in D)\land D\subseteq C\\
&\land\forall y(y\in D\to\varphi(y,p)).
\end{aligned}
```

Now define the exact response template

```math
\boxed{\begin{aligned}
W^{X,\Gamma}_{\rm game}(p,C):={}&
P_\varphi(p)\to\exists D\bigl[\mathrm{Pkt}_\varphi(D,p,C)\\
&\land\bigl(\mathrm{Empty}(t)\to\forall A\bigl[\\
&\quad\bigl(\mathrm{Pay}_X(\varphi,p,A)
\land(\Gamma(A)\land\mathrm{Ans}_X(A))^{J_t}\bigr)\\
&\quad\to\exists S\bigl(\mathrm{Plays}_X(D,S)\\
&\qquad\land(\mathrm{Coh}_X(S)\land\mathrm{Ans}_X(S))^{J_t}\bigr)
\bigr]\bigr)\bigr].
\end{aligned}}
```

Important: coherence is imposed on a selected packet D, not the entire C. The seed and different inputs can require mutually incompatible plays.

### Payoff classes, as first-order predicates

$`\mathrm{All}(A):=\mathrm{true}`$.

$`\mathrm{OD}(A)`$: there exist an ordinal $`\alpha`$, a formula code $`e\in\omega`$, and a finite tuple of ordinal parameters $`\beta_i<\alpha`$ such that A belongs to $`V_\alpha`$ and is the unique z in $`V_\alpha`$ with

```math
\mathrm{Sat}(V_\alpha,e,(z,\vec\beta)).
```

$`\mathrm{OD}(\mathbb R)(A)`$ is the same definition with one real parameter $`r\in\omega^\omega`$ also allowed; require $`r\in V_\alpha`$. A finite tuple of real parameters can be coded by one real. Sat is satisfaction for the set structure $`(V_\alpha,\in)`$, never satisfaction for the whole universe.

$`\mathrm{Bor}(A)`$, used only for $`X=\omega`$, means A is in every $`\sigma`$-algebra of subsets of $`\omega^\omega`$ containing all basic cylinders:

```math
\begin{aligned}
A\subseteq\omega^\omega\ \land
\forall\mathcal B\subseteq\mathcal P(\omega^\omega)\Bigl[&
\bigl(\forall s\in\omega^{<\omega}\,[s]\in\mathcal B\bigr)\\
&\land\bigl(\forall B\in\mathcal B\;\omega^\omega\setminus B\in\mathcal B\bigr)\\
&\land\bigl(\forall f:\omega\to\mathcal B\;
\bigcup\mathrm{ran}(f)\in\mathcal B\bigr)\\
&\to A\in\mathcal B\Bigr],
\end{aligned}
```

where $`[s]=\{r\in\omega^\omega:s\text{ is an initial segment of }r\}`$. The Borel row includes $`\mathrm{WO}_t`$ and thus uses its Choice calibration; no identification of alternative choiceless definitions of Borel sets is being assumed.

### Why this is the determinacy response

A coherent set S determines Player I's move at each history reached by S; give a fixed default move elsewhere. If S answers every II strategy, every play of the resulting I strategy belongs to S: prescribe the odd moves of a purported outside play as an II strategy and use uniqueness of the joint play. Conversely, all plays of an I-winning strategy are a coherent answering set. This proves the underlying game lemma in ZF for the two pointed move sets above. The additional bridge from raw packets and $`\mathrm{WO}_t`$ to the interpreted theory remains the research K-translation argument, not part of the cited determinacy theorem.

## 6. Structural responses

Fix a parameter $`\sigma`$ coding a countable first-order signature. A structure is a set code with a **nonempty** domain, interpretations of its relation and function symbols, and their finite arities. Products have choice functions as domain and coordinatewise interpretations. A homomorphism preserves operations and positive relations. An elementary embedding $`j:A\to B`$ is defined using set-structure satisfaction:

```math
\begin{aligned}
\forall e\in\mathrm{Form}(\sigma)\;
\forall\vec a\in A^{<\omega}\;\bigl[
&\mathrm{Sat}(A,e,\vec a)\\
&\leftrightarrow\mathrm{Sat}(B,e,j\vec a)\bigr].
\end{aligned}
```

Restrict e and assignments to the appropriate number of free variables. Sat is a uniform definable satisfaction relation for set structures; this does not require a truth predicate for the universe.

Define the activation condition

```math
\begin{aligned}
\mathrm{Gate}_\varphi(p):={}&
\mathrm{Empty}(t)\land J_t(\sigma)\land\mathrm{Sig}^{J_t}(\sigma)\\
&\land\forall y\,[\varphi(y,p)\to(J_t(y)\land\mathrm{Str}^{J_t}_\sigma(y))].
\end{aligned}
```

$`\mathrm{Fiber}(\varphi,p,C,F)`$ says F is the interpreted set of **all** represented $`\varphi`$-witnesses already in C:

```math
\begin{aligned}
J_t(F)\land\forall z\in J_t\;\bigl[z\,e_t\,F
\leftrightarrow{}&
\exists y(E(y,C)\land\varphi(y,p)\\
&\land J_t(y)\land y\sim_t z)\bigr].
\end{aligned}
```

Let $`\mathscr A_{\varphi,p}`$ be a class abbreviation, never a set variable:

```math
\begin{aligned}
B\in\mathscr A_{\varphi,p}\quad:\Longleftrightarrow\quad&
J_t(B)\\
&\land\exists y\,(\varphi(y,p)\land J_t(y)\land y\sim_t B).
\end{aligned}
```

The three certificates, with all set-theoretic quantifiers interpreted in $`J_t`$, are

```math
\begin{aligned}
\mathsf H_\times(F)&:=
\forall B\in\mathscr A_{\varphi,p}\;\exists h\;
h:\prod F\longrightarrow_{\rm hom}B,\\[6pt]
\mathsf H_{\rm el}(F)&:=
\forall B\in\mathscr A_{\varphi,p}\;\exists A\in F\;\exists j\;
j:A\longrightarrow_{\rm elem}B,\\[6pt]
\mathsf H_{\mathrm w\times}(F)&:=
\exists\kappa\,\exists S\,\bigl[\mathrm{InfCard}(\kappa)\\
&\quad\land\varnothing\ne S\subseteq F\cap V_\kappa\\
&\quad\land\forall X\,\bigl((X\le\prod S\land |X|\le\kappa)\\
&\qquad\to\forall B\in\mathscr A_{\varphi,p}\;\exists h\;
h:X\longrightarrow_{\rm hom}B\bigr)\bigr].
\end{aligned}
```

$`X\le\prod S`$ means substructure, and $`|X|\le\kappa`$ refers to the domain of X.

For j in {product, weak-product, elementary}, set

```math
\boxed{\begin{aligned}
W^j_{\rm struct}(p,C):={}&
P_\varphi(p)\to\bigl[\exists y(y\in C\land\varphi(y,p))\\
&\land\bigl(\mathrm{Gate}_\varphi(p)\to\\
&\quad\exists F\bigl[\mathrm{Fiber}(\varphi,p,C,F)\\
&\qquad\land(\prod F\ne\varnothing)^{J_t}\land\mathsf H_j(F)\bigr]\bigr)\bigr].
\end{aligned}}
```

The nonempty product is explicit. Omitting it can make a universal homomorphism requirement vacuous and loses the intended Choice argument. For the weak-product condition, the witnessing S is retained under later enlargement of F. A requirement on every small substructure of the *current full* product without a frozen bounded S would need a different monotonicity proof.

These are genuine first-order schemas even when $`\mathscr A_{\varphi,p}`$ is a proper class: each occurrence of $`B\in\mathscr A_{\varphi,p}`$ is replaced by its displayed formula. There is no quantification over proper classes.

## 7. The inaccessible row is a scope substitution

This row has an individual constant U, the same in every instance. It uses the **same original K kernel** in two scopes. U is not a fresh universally quantified input.

For a domain formula $`\Delta`$, membership formula e, and binary matrix $`\Psi`$, define

```math
\begin{aligned}
\mathrm{Core}_{\Delta,e}(\Psi):={}&
\forall a,x\in\Delta\;\exists C\in\Delta\bigl[\\
&(\Psi(x,a)\to e(x,C))\\
&\land\forall u\in\Delta\bigl(e(u,C)\to\bigl[\\
&\quad\exists p\in\Delta\;\Psi(u,p)\\
&\quad\land\forall p\in\Delta\bigl(
\mathrm{Sub}_{\Delta,e}(p,u)\to\\
&\qquad((\exists y\in\Delta\;\Psi(y,p))\\
&\qquad\quad\to\exists y\in\Delta(e(y,C)\land\Psi(y,p)))
\bigr)\bigr]\bigr)\bigr],
\end{aligned}
```

where

```math
\mathrm{Sub}_{\Delta,e}(p,u):=
\forall z(\Delta(z)\to(e(z,p)\to e(z,u))).
```

Only the template quantifiers are relativized. The bound variables inside the definitions of $`\Delta`$, e and $`\Psi`$ remain in their original scope.

The following uses the **whole quotient $`Q_t`$**, not just $`J_t`$.

```math
\begin{aligned}
\mathrm{Name}_t(v,z)&:=
(v=t\land D_t(z)\land\mathrm{Empty}^{Q_t}(z))\\
&\quad\lor(D_t(v)\land z=v),\\[4pt]
N_{t,U}(v)&:=v=t\lor(D_t(v)\land D_t(U)\land e_t(v,U)),\\[4pt]
e_t^*(v,w)&:=\exists z\exists z'\bigl[
\mathrm{Name}_t(v,z)\land\mathrm{Name}_t(w,z')\\
&\quad\land e_t(z,z')\bigr],\\[4pt]
\rho_{t,r}(v,w)&:=r=t\ \lor\ \bigl[D_t(r)\land\exists z\exists z'\bigl(\\
&\quad\mathrm{Name}_t(v,z)\land\mathrm{Name}_t(w,z')\\
&\quad\land(\langle z,z'\rangle\in r)^{Q_t}\bigr)\bigr].
\end{aligned}
```

The special name t denotes the quotient-empty object. The special relation parameter $`r=t`$ denotes the universal relation. Neither is an uncounted new symbol.

Let $`l:=\mathrm{Empty}(t)\land d=t`$. Make the Boolean substitutions

```math
\begin{aligned}
\Delta_l(v)&:=(\neg l)\lor N_{t,U}(v),\\
e_l(v,w)&:=(\neg l\land E(v,w))\lor(l\land e_t^*(v,w)),\\
\Psi_l(v,w)&:=(\neg l\land\varphi(v,w))\lor(l\land\rho_{t,r}(v,w)).
\end{aligned}
```

The scoped theory consists of the universal closures, except for U, of

```math
\boxed{\mathrm{Core}_{\Delta_l,e_l}(\Psi_l).}\tag{L}
```

This is one literal schema in $`L(U)`$, not 'U models all formulas' and not an uncounted second-order quantifier. Local quantification is over actual set-coded relations r in $`Q_t`$. Ordinary K is recovered in the global case; the universal local relation rules out the degenerate all-empty raw structure. The published original K interpretation alone does not certify the claimed inaccessible calibration of this **new** two-scope theory; the full-relations-to-universe reduction needs independent checking.

## 8. What is established, what is research

The exact original K schema and its ZFC equiconsistency are upstream formal results. The PA schema has a checked reference generator and finite semantic tests, but its imported nonextensional interpretation has a separate proof obligation. The member-request $`Z_2`$ schema and all advanced K translations have mathematical arguments in the conversation, not independently certified theorems in the pinned K repository.

Published results establish the **conventional** target calibrations:

- ZFC proves Borel determinacy.
- ZFC+OD-determinacy is equiconsistent with ZFC+one Woodin; ZFC+OD(R)-determinacy with ZFC+$`\omega`$-many Woodins.
- Over ZFC, the all-definable-class product, weak-product and elementary reflection schemes correspond respectively to 'Ord is Woodin', 'Ord is essentially subtle', and Vopenka's principle.

The additional raw-K-to-interpreted-principle bridges are new. A public table should mark those entries as research rather than implying the published papers proved these exact new schemas.

The combined all-payoffs integer-game response and $`\mathrm{WO}_t`$ condition is a **negative control**, not a consistent catalogue row: if the intended interpretation bridge is established, it implies AD and AC in the same $`J_t`$, hence inconsistency. Ordinary K being equiconsistent with ZFC does not mean raw K itself assumes AC.

## 9. Primary sources and reproducible anchors

1. Original K: elliotglazer/k230-rocq at `a8312f0ca703bc81baac16695a437a7d3788f690`, `docs/proof-overview.md`, `coq/settheory/KPrimeCore.v`, `KQuot.v`, and `KOrderedPair.v`.
   https://github.com/elliotglazer/k230-rocq/tree/a8312f0ca703bc81baac16695a437a7d3788f690
2. PA companion notes: Mira-Cult/turing-machines at `3e08d06dd4618a99d0e67e7856de549908d3a4f2`, `research/model-games/docs/K_FINITE_COMPANION.md`.
3. Peter Koellner and W. Hugh Woodin, *Large Cardinals from Determinacy*, especially Section 6, Theorems 6.1/6.2 and their equiconsistency consequences.
   https://bpb-us-e1.wpmucdn.com/websites.harvard.edu/dist/f/94/files/2022/07/LCFD.pdf
4. Joan Bagaria and Philipp Luecke, *Patterns of Structural Reflection in the large-cardinal hierarchy*, arXiv:2210.07120v2 (2023), Theorems 1.6, 1.27, 1.33; definition 1.29.
   https://arxiv.org/abs/2210.07120
5. Vladimir Kanovei and Vassily Lyubetsky, *Notes on the Equiconsistency of ZFC Without the Power Set Axiom and Second-Order Arithmetic*, Axioms 14 (2025), 865. This is a conventional equiconsistency result, not a proof of K_mem's reduction.
   https://doi.org/10.3390/axioms14120865

No machine size, shortest-schema claim, formal verification result, or new publication is claimed by this definitions document.
