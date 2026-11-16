# A nilpotent-residual splitting for odd metabelian derived groups

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with two independent exact-source acceptances recorded below.** It is a group theorem that applies to every finite odd group G equipped with an involution τ when its derived group D=G′ is metabelian. It does not assume an exact-factorization folder or a coprime splitting of D′ from D/D′. For the simple odd Bol application, τ and G=HD are the reviewed canonical-folder inputs. The result supplies a group/module normal form, not yet a loop classification.

## The canonical residual and mixed-prime splitting

Put M=D′=G″, which is abelian and characteristic in G. If D is already nilpotent, the conclusion holds with R=1,N=D,L=G; hence assume below that its nilpotent residual is nontrivial. Since D/M is abelian, it acts on M by commuting automorphisms. Let J be the augmentation ideal of the finite commutative ring (Z/exp(M)Z)[D/M] acting on M. Its powers stabilize: choose n with J^n=J^{n+1}. The stable ideal I=J^n is idempotent and finitely generated. Choose generators x_i and express x_i=∑_j a_ij x_j with a_ij∈I. The determinant trick gives (1−e)I=0 for some e∈I; hence e²=e and I=eR₀, where R₀ is the ring. Consequently

    M=R⊕C,  R=J^n M,  C=ann_M(J^n),  JR=R,  J^n C=0.      (1)

The subgroups are characteristic under automorphisms of D. Moreover R is the nilpotent residual γ∞(D): for i≥2, γ_{i+1}(D)=Jγ_i(D), since γ_i(D)≤M, so the lower central series stabilizes at J^nM. It follows that Q=D/R is nilpotent.

Fix a prime p dividing |R|. Let B_p be the characteristic p′-Hall subgroup of the finite nilpotent group Q, and Q_p its p-Sylow subgroup. R is abelian, so Q acts on R_p. The coprime averaging idempotent for B_p makes F=R_p^{B_p} a Q_p-invariant direct summand. Projecting JR_p=R_p to F gives F=[F,Q_p], because Q=B_p×Q_p and B_p acts trivially on F. The augmentation ideal of a finite p-group is nilpotent over F_p: induct on the group order, choosing a central element z of order p; (z−1)^p=0 and the quotient by (z−1) is the smaller group algebra. If its augmentation ideal has nilpotency index k, the original has index at most kp. On a finite abelian p-group module, reduce modulo p and iterate through its finite p-power filtration. Thus an augmentation-surjective nonzero module F is impossible. Hence F=0. Therefore

    R_p^{B_p}=0 for every p | |R|.                            (2)

## Local Hall normalizers and the global τ-compatible splitting

No cohomology or initial splitting of the involution quotient is needed. For each p dividing |R|, let R_{p′}=∏_{r≠p}R_r and set

    E_p=(D/R_{p′})⋊<τhat>,    Γ=(D/R)⋊<τhat>.

The kernel of E_p→Γ is R_p. In Γ the characteristic p′-Hall B_p of the nilpotent group D/R is normal. Its inverse image V_p in E_p has R_p as a normal Hall subgroup, so it has B_p-complements by Schur–Zassenhaus. To choose one normalized by the actual formal τhat, work in the inverse image of B_p⋊<τhat>: its quotient has order 2|B_p|, coprime to p. A Hall complement exists, and its outside involution is R_p-conjugate to τhat inside R_p⋊<τhat>. Its B_p-part B₀ is then normalized by the actual τhat.

The subgroup V_p is normal in E_p, and its B_p-complements are R_p-conjugate. The Frattini argument gives E_p=R_p N_{E_p}(B₀). The kernel R_p∩N_{E_p}(B₀) is C_{R_p}(B₀), because commutators of an R_p-normalizer with B₀ lie in R_p∩B₀. It is trivial by (2). Thus N_{E_p}(B₀) maps isomorphically to Γ and contains τhat. This constructs a τ-compatible local Γ-complement without assuming any prior quotient splitting.

The natural map from D⋊<τhat> to the fiber product of the E_p over Γ is injective, since ∩_p R_{p′}=1, and both groups have order |R||Γ|. It is therefore an isomorphism. The fiber product of the local normalizer complements gives a global Γ-complement containing τhat. Its intersection with D is a τ-stable nilpotent complement N≤D, with D=R⋊N and N≅D/R.

Every complement to R in D is R-conjugate: their local images are unique up to R_p-conjugacy by the normalizer construction, and the conjugators assemble through R=∏R_p. Hence the Frattini argument gives G=R N_G(N). Moreover C_R(N)=1 by (2), since the p′-Hall B_p of N has no fixed points on R_p. An r∈R normalizing N must centralize N because [r,N] lies in R∩N=1. Therefore

    G=R⋊L,  L=N_G(N),  N◁L,  L′=N,  L/N≅G/D,
    τ(L)=L, τ(N)=N.                                           (3)

The equality L′=N follows because G/R≅L and G′/R=D/R≅N. Also D′=R⊕N′: [R,N]=R, and R∩N′=1. The nilpotent group N is metabelian, and its action on R obeys (2), although |R| and |N| may share primes and the own-p part of N may act nontrivially on R_p. In (1), the complementary summand C equals N′: its action by N is nilpotent and M=R⊕N′, identifying it with the nilpotent Fitting summand. If R=1 the statement reduces to the original nilpotent-derived branch.

This is stronger than a generic chief-extension enumeration: the entire nonnilpotent residual splits canonically up to conjugacy, with fixed-point-free action of a specified p′-Hall subgroup at each prime, and a common τ-compatible complement. It does not imply that N is abelian, that R and N have coprime orders, or that A=L/N has a complement in L.

## Concrete next branch

For a canonical simple odd folder, define W=H∩R and J=HR/R≤L. The original stabilizer is an extension graph in (R/W)⋊J once W is identified; its lift must be retained as an actual 1-cocycle, not normalized away while τ and K stay fixed. The remaining obstruction is to describe the J-action, τ-compatible cocycle and normal-subgroup/marked-fiber constraints while retaining the nilpotent metabelian kernel N. The Q_{p,q} examples are the special case N=C_q² abelian, with R=V² and coprime factors; previously constructed central class-two examples are in R=1. A complete branch theorem would still require finite construction, transversality, all τ-stable-normal simplicity and actual-loop isomorphism tests. No universal classification or proof that every such structural datum yields a loop is claimed.

The determinant trick and augmentation-nilpotence arguments are proved inline. The Hall existence/conjugacy input is Schur–Zassenhaus, as used in the [reviewed coprime-center argument](odd-class-two-coprime-center-reduction.md) at `30d3ddf2d4a99650d08b4add502402a383f91447`; no new primary-source audit is claimed here. At exact source `7530ae6eeeb0614d7c94ed6ab1f6761f3493ab88`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the complete group theorem under its Schur–Zassenhaus input. Both checked the stable augmentation ideal, intrinsic residual and complementary summand, local fixed-point vanishing, actual-involution Hall alignment, fiber-product assembly, conjugacy of complements and normalizer splitting, including C=N′ and possible prime overlap. Neither acceptance asserts a loop classification. No computation, formal verification or literature novelty is claimed.
