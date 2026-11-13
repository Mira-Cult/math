# A guarded arithmetic-circuit generator for integer detection

This note describes [`code/generate.py`](code/generate.py) (2,518 ASCII bytes).
The source is JoseBrox/diophantine-z-q_improvements at commit
`fa09c9c6c97982c13265e7088d95cdb61b3e90cf`, principally
`papers/quartic/quartic262_20261110_v21.tex` and
`papers/arithmetic_dependencies/arithmetic_dependencies_20261108_v8.tex`.

**Arithmetic scope:** the resulting integer-detection assertion is conditional
on precisely the inherited arithmetic inputs stated by that source: the
specified elliptic group and index-height statements, full normalized modular
realization and the resulting contact-height estimate, pole obstruction and
zero-preparation realization, and simultaneous prime selection with the stated
congruence and approximation properties. The code does not prove these inputs.
No additional abc assumption is added. The compiler statements below are
unconditional.

## 1. Exactly what the program prints

The program is Python 3, requires no imports, makes no network calls, and prints
a finite expression using integer constants, powers to fixed nonnegative
integer exponents, variables `x0`, `x1`, ..., addition, subtraction and
multiplication. Interpret these variables as indeterminates, not Python
variables awaiting numerical initialization. The expression is a polynomial
over the integers. Its distinguished input is `x0`.

Every call to `v()` allocates a new variable. Every call to `g(e)` allocates a
new variable `z` and appends the residual `z-e`. A scalar division `a/b`
allocates `z`, appends `b*z-1`, and returns the product `a*z`. In particular,
division does not merely cross-multiply an equation whose two sides could
both vanish. It requires an actual inverse. Constants such as `149**19365`
are integer coefficients; they are never free variables.

The final output is the sum of the squares of all residuals. Over the rational
numbers this polynomial vanishes if and only if every residual vanishes.
Inducting through allocation order shows that all gate values are uniquely
determined by the original free coordinates, all division denominators are
nonzero, and the equations express exactly the arithmetic operations used in
the program. Conversely, any defined rational evaluation of the high-level
circuit satisfying its explicitly zeroed equations extends uniquely to gate
values at which the printed polynomial vanishes.

The class `K` implements ordered pairs `(a,b)` representing `a+b*sqrt(2)`.
It uses `(a,b)(c,d)=(ac+2bd,ad+bc)`, conjugation `(a,-b)`, and norm `a*a-2*b*b`.
Division divides the product with the conjugate by that norm, using the scalar
inverse rule. Thus the program uses rational coordinates throughout, rather
than quantifying over an algebraic extension implicitly. Since 2 is not a
rational square, zero norm is equivalent to the field element being zero.

Execution yields 3,779 variables, 3,751 squared residuals, and a 99,396-character
polynomial expression. Its total degree is exactly four. Scalar powers are
compiled recursively into multiplication gates, so every residual has degree
at most two. There are 1,588 quadratic residuals and 2,163 linear residuals.
At least one quadratic homogeneous part is nonzero; the top-degree part of
a sum of squares of real polynomials cannot vanish identically unless every
corresponding homogeneous part vanishes. Thus the total degree is exactly
four. None of the input coefficients depends on any quantified coordinate.

## 2. Elliptic coordinates and the stronger affine guards

Put

    K = Q(sqrt(2)),  D = 11-6*sqrt(2),  E: y^2=x^3-D*x,
    P = ((57-28*sqrt(2))/8, (-660+417*sqrt(2))/32).

`point()` allocates the two field coordinates of a point R on E, imposes its
curve equation, and returns its ordinary affine double. It requires `2*y(R)`
to be nonzero. Consequently every point it returns lies in `2E(K)=Z*P` and
is nonzero. A returned torsion point would be zero because the specified
group of doubles is torsion-free, and a zero double would require R to be
two-torsion, contrary to the nonzero denominator.

The program creates four root points `Q_i=[n_i]P`, four auxiliary points U_i,
and a common point H, all as doubles. The root indices are nonzero. In the
source notation `(n_1,n_2,n_3,n_4)=(n,a,t,b)`.

`sub(A,B)` is the ordinary chord formula for A-B and guards `x(A)-x(B)`.
It is used for H-P, U_i-Q_i, and Q_2-P. Its guard excludes respectively
H=+-P, U_i=+-Q_i, and Q_2=+-P. These are additional restrictions relative to
some exceptional branches allowed by the source. They preserve soundness and
do not destroy completeness: the source selects

    H=[h]P,  U_i=[n_i*h]P,  U_i-Q_i=[n_i*(h-1)]P

with arbitrarily large h in a prescribed progression and with all n_i
nonzero. Choose h>2. The scalar construction chooses a-1 arbitrarily large,
so a is not +-1. The group is torsion-free, hence all these subtraction
denominators are nonzero. Every chosen point lifts to an affine point before
doubling, since P=2R_0 for the non-torsion point
R_0=(1+sqrt(2),2*sqrt(2)).

All divisions defining `z(A)=-x(A)/y(A)` and `f(A)=1/x(A)` are guarded.
For the complete witnesses above, their arguments are non-torsion points,
so neither a zero ordinate nor a zero abscissa can occur. For soundness the
guards directly impose the same fact. Requiring H itself to lie in Z*P
only restricts the source's broader common-point domain and is consistent
with all witnesses constructed in its completeness proof.

## 3. The scalar certificate is unchanged mathematically

Write `beta=51*X^2+2504`, `ell=149`, `A_N=149^19365`, and

    r = beta*(beta-1)*(beta-2401)*(32*beta+343)*(2*beta-1),
    R = A_N*r/(1+ell^2*r).

These are the source's scalar normalizer at N=9682. In particular R>0 for
every rational X. The program takes

    Z=z(Q_2-P)/z(H),  F=Norm(f(H)),
    A=(Z_0^2+R*Z_1^2)/R^4,
    W_s=(A^2+R*F^2)/R^4,
    b_s=R*(R+9792)*W_s^2.

This is exactly the source's scalar norm certificate. The source's optimized
fixed-subtraction and common-point charts have been replaced by the actual
guarded group formulas, not by an approximation. Since f(H) is nonzero, F
is nonzero, W_s>0 and b_s>0.

For a scalar b the function `pole(b)` imposes the original zero-preparation
predicate from the arithmetic-dependency paper. With B=17b, it is

    p^2=B*(1-e)*(1+3e),
    B*q^2=(s^2-B*h_0)*(s^2+3*B*h_0),  h_0=e*(B-b^2).

The four witnesses e,p,q,s are rational and otherwise unrestricted. This
uses the unparametrized predicate, so it needs neither a conic chart nor
finite-root elimination. The source's pole obstruction and realization
input apply to exactly this predicate when b is nonzero.

It follows, by the source's scalar-extraction argument, that with c=|a-1|,

    149^45988 * M_5(beta)^3 divides c,
    c >= 149^45988,  h(beta) < c/40.

## 4. Uniform local products replace the packed factors

Let V_0=H-P and V_i=U_i-Q_i. Define

    L_i=z(U_i)/z(H),
    C_i=L_i-conjugate(z(V_i)/z(V_0)),
    I=L_1-beta,
    G=L_3^2-L_2*(L_2-2)*L_3*L_4+(L_2-2)^2*L_4^2-1.

The reciprocal-abscissa list has ten elements:

    f(H), f(U_1),...,f(U_4), conjugate(f(V_0)),...,conjugate(f(V_4)).

The comparison list has six elements: C_1,...,C_4,I,G.

Set S=sum(x(Q_i))=S_0+S_1*sqrt(2). The three scalar scales are
1,S_0^2,(S_0+S_1)^2, as in the explicit source. Put

    Theta={0,-1/2,-1,1/2399,-32/407},
    F_2(t)=product((t-theta)*(t-2+theta),theta in Theta),
    q=(t-1)^10/F_2(t)-1,    t=scale*lambda.

The denominator guard excludes every contact. Since zero is a contact,
lambda is automatically nonzero. The later guard on q+1 also excludes t=1,
so R_t=1/(q+1)=F_2(t)/(t-1)^10 is nonzero. These exclusions are harmless
in completeness, where lambda may be chosen arbitrarily large.

The new local product is

    W=product(1+q^3*f^2, f in the ten-element list)
      *product(1+q^5*c^2, c in the six-element list).

Write W=w_0+w_1*sqrt(2), set tau=Norm(W)/(2*w_0), and impose
`pole((408/409)^2*tau^2/(q+1))`. The division guard ensures w_0 is nonzero.
Therefore W, its norm, tau, and this pole input are all nonzero.

At a contact prime outside the source's fixed exceptional set, let
nu=v_p(R_t)>0 be odd. Then v(q)=-nu at every place above p. In each local
factor, the nonconstant term has odd valuation, so it cannot cancel 1.
Every factor is nonzero and has valuation at most zero; valuation zero
means that its residue is one. Put l=max_{v|p}v(W), which is at most zero.
Since tau=1/Tr(W^-1), the same trace inequality and pole obstruction as
in the source give l>-nu/2. Each factor and each of its nonconstant terms
has valuation greater than -nu/2. Hence

    v(f)>5*nu/4,    v(c)>9*nu/4.

Thus every reciprocal-abscissa test has order at least two and every
comparison test has order at least three. These imply all the source's
required orders, including the order-one input comparisons. Conjugate
places and inert primes are handled by the same trace argument.

The program need not exclude q=0 separately. If q=0, there is no contact
prime at that scale (since such a prime would give v(q)=-nu). Its contact
radical is therefore one. The subsequent height inequalities include
this case. No computation divides by q.

## 5. Soundness and completeness

The formal-group comparisons in the source now apply with stronger local
orders. If `(n,a,t,b)` are the four root indices and B is their maximum
absolute value, the same three contact radicals satisfy

    M_j^3 divides t^2-a*(a-2)*t*b+(a-2)^2*b^2-1,
    M_j divides the reduced numerator of n-beta.

The source's contact-height and effective abscissa-sum inequalities,
its exact N=9682 numerical bounds, and its Lucas descent are unchanged.
They force the first residual to be zero and then n=beta. Thus beta is
an integer. If X=u/v in lowest terms, integrality of 51X^2+2504 gives
v^2|51; since 51 is squarefree, v=1 and X is an integer.

Conversely, start with an integer X and carry out the source's
simultaneous completeness construction, avoiding the finite elliptic
exceptions listed above. At a selected contact prime, the construction
has nu=1, reciprocal-abscissa values of valuation at least two, and
all six comparison values of valuation at least four. The new factors
therefore are all congruent to one. Away from selected contact primes,
the same even-denominator and local-square preparation applies.
At the fixed primes 2,3,17 the source prepares sufficiently negative
valuations of lambda, while at both real embeddings it makes lambda
sufficiently large and positive. These compatible prescribed conditions
make q tend to zero and W tend to one in the respective completions. Consequently the new pole inputs have the same
required square-denominator, local-square, valuation and 0<b<17
properties as the source inputs. The zero-preparation pole-realization
premise supplies rational witnesses independently for each input.
The scalar pole is unchanged. All added inverse guards are satisfied,
and the compiler extends these witnesses to a zero of the printed
polynomial.

Subject to the stated arithmetic premises, therefore,

    {x in Q : exists rational x1,...,x3778 with F(x,x1,...)=0}=Z.

The uniform-product local lemma and the guarded compiler are new
simplifications of the presentation; the deep arithmetic implications
remain inherited, rather than re-proved by executing the generator.
