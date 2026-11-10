import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactLeastCounterexample

/-! Capture-safe alpha conversions needed to match the displayed candidate
domain syntax. These are K proof-data constructions, not extensionality or
semantic soundness arguments. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename both transitivity test binders using pointwise instantiation and
generalization with freshly displayed names. -/
def transitive_rename (x s t p q : Nat) (fresh : [x,s,t,p,q].Nodup) :
    KDerivation (imp (transitiveCode x s t) (transitiveCode x p q)) := by
  have hsx : s ≠ x := by intro h; subst s; simp at fresh
  have hsp : s ≠ p := by intro h; subst s; simp at fresh
  have hst : s ≠ t := by intro h; subst s; simp at fresh
  have htx : t ≠ x := by intro h; subst t; simp at fresh
  have htp : t ≠ p := by intro h; subst t; simp at fresh
  have htq : t ≠ q := by intro h; subst t; simp at fresh
  have hpx : p ≠ x := by intro h; subst p; simp at fresh
  have hps : p ≠ s := by intro h; subst p; simp at fresh
  have hpt : p ≠ t := by intro h; subst p; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hqs : q ≠ s := by intro h; subst q; simp at fresh
  have hqt : q ≠ t := by intro h; subst q; simp at fresh
  let T := transitiveCode x s t
  let Γ := [T]
  have ht : Context Γ T := Context.head [] T
  have hp : Context Γ (imp (member x p) (imp (member p q) (member x q))) :=
    .mp ht (.closed (transitive_chain x s t p q hsx hsp hst htx htp htq))
  have hvp : ∀ h, h ∈ Γ → KDerivation (imp h (allCode p h)) := by
    intro h hh
    have he : h = T := by simpa [Γ] using hh
    subst h
    exact transitive_vacuity x s t p hpx hps hpt
  have hvq : ∀ h, h ∈ Γ → KDerivation (imp h (allCode q h)) := by
    intro h hh
    have he : h = T := by simpa [Γ] using hh
    subst h
    exact transitive_vacuity x s t q hqx hqs hqt
  have hr : Context Γ (transitiveCode x p q) := Context.generalize p hvp (Context.generalize q hvq hp)
  exact Context.closeEmpty (Context.deduction hr)

/-- Rename the order-test binder in a least-member formula. -/
def least_member_rename (u m r z : Nat) (fresh : [u,m,r,z].Nodup) :
    KDerivation (imp (leastMemberCode u m r) (leastMemberCode u m z)) := by
  have hru : r ≠ u := by intro h; subst r; simp at fresh
  have hrm : r ≠ m := by intro h; subst r; simp at fresh
  have hrz : r ≠ z := by intro h; subst r; simp at fresh
  have hzu : z ≠ u := by intro h; subst z; simp at fresh
  have hzm : z ≠ m := by intro h; subst z; simp at fresh
  let f : CompactNamed.Formula := .imp (.member u r) (namedEither (.equal r m) (.member r m))
  have ha := CompactNamed.universalAlpha r z f hrz
    (by simp [f, namedEither, CompactNamed.Formula.binders])
    (by simp [f, namedEither, CompactNamed.Formula.names, hzu, hzm, Ne.symm hrz])
  have ha' : KDerivation (imp (allCode r (imp (member u r) (either (equal r m) (member r m))))
      (allCode z (imp (member u z) (either (equal z m) (member z m))))) := by
    simpa [f, namedEither, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      CompactProof.neg, CompactDerivations.either, hru, hrm, hrz, hzu, hzm,
      Ne.symm hru, Ne.symm hrm, Ne.symm hrz, Ne.symm hzu, Ne.symm hzm] using ha.1
  apply Context.closeEmpty
  apply Context.deduction
  have hl : Context [leastMemberCode u m r] (leastMemberCode u m r) := Context.head [] _
  exact Context.conjunctionIntro (Context.conjunctionLeft hl)
    (.mp (Context.conjunctionRight hl) (.closed ha'))

/-- Rename the least-order-test binder throughout the least-subset property. -/
def least_subsets_rename (x u k a m r z : Nat) (fresh : [x,u,k,a,m,r,z].Nodup) :
    KDerivation (imp (leastSubsetsCode x u k a m r) (leastSubsetsCode x u k a m z)) := by
  have hnames : [u,m,r,z].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have he := existsCongr m (least_member_rename u m r z hnames)
  have hp : KDerivation (imp
      (imp (subsetCode u x k) (imp (nonemptyCode u a) (existsCode m (leastMemberCode u m r))))
      (imp (subsetCode u x k) (imp (nonemptyCode u a) (existsCode m (leastMemberCode u m z))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [nonemptyCode u a, subsetCode u x k,
      imp (subsetCode u x k) (imp (nonemptyCode u a) (existsCode m (leastMemberCode u m r)))]
    have hn : Context Γ (nonemptyCode u a) := .hypothesis (by simp [Γ])
    have hs : Context Γ (subsetCode u x k) := .hypothesis (by simp [Γ])
    have hi : Context Γ (imp (subsetCode u x k)
        (imp (nonemptyCode u a) (existsCode m (leastMemberCode u m r)))) := .hypothesis (by simp [Γ])
    exact .mp (.mp hn (.mp hs hi)) (.closed he)
  exact allCongr u hp

end PASoundness.PAtoCompactCandidateAlpha

#print axioms PASoundness.PAtoCompactCandidateAlpha.transitive_rename
#print axioms PASoundness.PAtoCompactCandidateAlpha.least_subsets_rename
