import PASoundness.PAtoCompactGreatestDownward
import PASoundness.PAtoCompactTransitiveDomain
import PASoundness.PAtoCompactDomainClassification

/-! The explicit member-domain schema follows from the outer set's
one-level transitive-member fragment and greatest-subset condition. These
properties themselves are hypotheses; no full arithmetic interpretation is
asserted. Code 1 is literal self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOuterDomain
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactGreatestDownward
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactDomainClassification
open PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- In a transitive set, each member is a represented subset. -/
def transitive_member_subset (x m p q k : Nat) (fresh : [x,m,p,q,k].Nodup) :
    KDerivation (imp (transitiveCode x p q) (imp (member x m) (subsetCode m x k))) := by
  have hpx : p ≠ x := by intro h; subst p; simp at fresh
  have hpm : p ≠ m := by intro h; subst p; simp at fresh
  have hpq : p ≠ q := by intro h; subst p; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hqm : q ≠ m := by intro h; subst q; simp at fresh
  have hqk : q ≠ k := by intro h; subst q; simp at fresh
  have hkx : k ≠ x := by intro h; subst k; simp at fresh
  have hkm : k ≠ m := by intro h; subst k; simp at fresh
  have hkp : k ≠ p := by intro h; subst k; simp at fresh
  have hkq : k ≠ q := by intro h; subst k; simp at fresh
  let T := transitiveCode x p q
  let X := member x m
  let Γ := [X,T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hi : Context Γ (imp (member m k) (member x k)) :=
    .mp hx (.mp ht (.closed (transitive_chain x p q m k hpx hpm hpq hqx hqm hqk)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode k h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = X
    · subst h
      exact membershipVacuity x m k hkx hkm
    · have he' : h = T := hh.resolve_left he
      subst h
      exact transitive_vacuity x p q k hkx hkp hkq
  have hout : Context Γ (subsetCode m x k) := Context.generalize k hv hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hout

/-- The quantified member-domain condition used in classification follows
from explicit outer transitivity, transitive members, and greatest subsets.
The outer and inner greatest-subset binders a and u are distinct. -/
def all_members_domain (x m p q b a k y t u s : Nat)
    (fresh : [x,m,p,q,b,a,k,y,t,u,s].Nodup) :
    KDerivation (imp (oneLevelTransitiveCode x b p q)
      (imp (greatestSubsetsCode x a k y t) (allMembersDomainCode x m p q u k y t))) := by
  have hbx : b ≠ x := by intro h; subst b; simp at fresh
  have hbm : b ≠ m := by intro h; subst b; simp at fresh
  have hbp : b ≠ p := by intro h; subst b; simp at fresh
  have hbq : b ≠ q := by intro h; subst b; simp at fresh
  have hmp : m ≠ p := by intro h; subst m; simp at fresh
  have hmq : m ≠ q := by intro h; subst m; simp at fresh
  have hmx : m ≠ x := by intro h; subst m; simp at fresh
  have hmb : m ≠ b := by intro h; subst m; simp at fresh
  have hma : m ≠ a := by intro h; subst m; simp at fresh
  have hmk : m ≠ k := by intro h; subst m; simp at fresh
  have hmy : m ≠ y := by intro h; subst m; simp at fresh
  have hmt : m ≠ t := by intro h; subst m; simp at fresh
  have hf1 : [x,m,p,q,k].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have hf2 : [x,m,a,k,y,t,u,s].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  let T := transitiveCode x p q
  let M := membersTransitiveCode x b p q
  let G := greatestSubsetsCode x a k y t
  let Γ := [G,M,T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (member x m)
      (both (transitiveCode m p q) (greatestSubsetsCode m u k y t))) := by
    apply Context.deduction
    let Δ := member x m :: Γ
    have hx : Context Δ (member x m) := Context.head _ _
    have htm : Context Δ (transitiveCode m p q) := .mp hx
      (.mp (Context.under hm _) (.closed (member_transitive_instance x b p q m hbx hbm hbp hbq hmp hmq)))
    have hs : Context Δ (subsetCode m x k) := .mp hx
      (.mp (Context.under ht _) (.closed (transitive_member_subset x m p q k hf1)))
    have hgm : Context Δ (greatestSubsetsCode m u k y t) := .mp hs
      (.mp (Context.under hg _) (.closed (greatest_subsets_downward x m a k y t u s hf2)))
    exact Context.conjunctionIntro htm hgm
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode m h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = G
    · subst h
      exact greatest_subsets_vacuity x a k y t m hmx hma hmk hmy hmt
    · by_cases he' : h = M
      · subst h
        exact members_transitive_vacuity x b p q m hmx hmb hmp hmq
      · have he'' : h = T := (hh.resolve_left he).resolve_left he'
        subst h
        exact transitive_vacuity x p q m hmx hmp hmq
  have hall : Context Γ (allMembersDomainCode x m p q u k y t) := Context.generalize m hv hpoint
  have hc : KDerivation (imp T (imp M (imp G (allMembersDomainCode x m p q u k y t)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    exact hall
  -- Project the conjunction to discharge the two component assumptions.
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Δ := [G,oneLevelTransitiveCode x b p q]
  have hd : Context Δ (oneLevelTransitiveCode x b p q) := .hypothesis (by simp [Δ])
  have hg' : Context Δ G := .hypothesis (by simp [Δ])
  exact .mp hg' (.mp (Context.conjunctionRight hd) (.mp (Context.conjunctionLeft hd) (.closed hc)))

theorem all_members_domain_certificate (x m p q b a k y t u s : Nat)
    (fresh : [x,m,p,q,b,a,k,y,t,u,s].Nodup) :
    theoremCode (certificate (all_members_domain x m p q b a k y t u s fresh)) =
      imp (oneLevelTransitiveCode x b p q)
        (imp (greatestSubsetsCode x a k y t) (allMembersDomainCode x m p q u k y t)) :=
  certificate_correct (all_members_domain x m p q b a k y t u s fresh)

/-- Classification of every outer member from those same outer hypotheses;
the previously separate all-members-domain schema is constructed in K. -/
def all_members_classification_outer (x m p q b a k y t u s w z : Nat)
    (fresh : [x,m,p,q,b,a,k,y,t,u,s,w,z].Nodup) :
    KDerivation (imp (oneLevelTransitiveCode x b p q)
      (imp (greatestSubsetsCode x a k y t) (allClassificationCode x y m z w p q))) := by
  have hf1 : [x,m,p,q,b,a,k,y,t,u,s].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have hf2 : [m,p,q,u,k,y,t,w].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have hpx : p ≠ x := by intro h; subst p; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hmx : m ≠ x := by intro h; subst m; simp at fresh
  have hyx : y ≠ x := by intro h; subst y; simp at fresh
  have hym : y ≠ m := by intro h; subst y; simp at fresh
  have hyp : y ≠ p := by intro h; subst y; simp at fresh
  have hyq : y ≠ q := by intro h; subst y; simp at fresh
  have hyz : y ≠ z := by intro h; subst y; simp at fresh
  have hzm : z ≠ m := by intro h; subst z; simp at fresh
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let D := oneLevelTransitiveCode x b p q
  let G := greatestSubsetsCode x a k y t
  let Γ := [G,D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hmembers : Context Γ (allMembersDomainCode x m p q u k y t) :=
    .mp hg (.mp hd (.closed (all_members_domain x m p q b a k y t u s hf1)))
  exact .mp hmembers (.mp (Context.conjunctionLeft hd) (.closed
    (all_members_classification x m p q u k y t w z hf2 hpx hqx hmx hyx hym hyp hyq hyz hzm)))

theorem all_members_classification_outer_certificate (x m p q b a k y t u s w z : Nat)
    (fresh : [x,m,p,q,b,a,k,y,t,u,s,w,z].Nodup) :
    theoremCode (certificate (all_members_classification_outer x m p q b a k y t u s w z fresh)) =
      imp (oneLevelTransitiveCode x b p q)
        (imp (greatestSubsetsCode x a k y t) (allClassificationCode x y m z w p q)) :=
  certificate_correct (all_members_classification_outer x m p q b a k y t u s w z fresh)

end PASoundness.PAtoCompactOuterDomain

#print axioms PASoundness.PAtoCompactOuterDomain.all_members_domain
#print axioms PASoundness.PAtoCompactOuterDomain.all_members_domain_certificate
#print axioms PASoundness.PAtoCompactOuterDomain.all_members_classification_outer
#print axioms PASoundness.PAtoCompactOuterDomain.all_members_classification_outer_certificate
