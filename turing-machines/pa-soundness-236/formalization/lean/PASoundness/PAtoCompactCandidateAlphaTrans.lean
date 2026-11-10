import PASoundness.PAtoCompactCandidateAlpha
import PASoundness.PAtoCompactTransitiveDomain

/-! Capture-safe renaming of both transitivity test binders in the full
one-level fragment. This constructs finite K proof data; it does not assume
semantic soundness, extensionality, or an arithmetic interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateAlphaTrans
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactCandidateAlpha

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Renaming the transitivity-test names throughout the condition on every
immediate member. Its outer member binder remains b. -/
def members_transitive_tests_rename (x b s t p q : Nat)
    (fresh : [x,b,s,t,p,q].Nodup) :
    KDerivation (imp (membersTransitiveCode x b s t) (membersTransitiveCode x b p q)) := by
  have hb : [b,s,t,p,q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hi : KDerivation (imp (imp (member x b) (transitiveCode b s t))
      (imp (member x b) (transitiveCode b p q))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member x b, imp (member x b) (transitiveCode b s t)]
    have hm : Context Γ (member x b) := Context.head _ _
    have ht : Context Γ (imp (member x b) (transitiveCode b s t)) := .hypothesis (by simp [Γ])
    exact .mp (.mp hm ht) (.closed (transitive_rename b s t p q hb))
  exact allCongr b hi

/-- Both outer transitivity and transitivity of all members are renamed to
the same two fresh test binders. The member binder is unchanged. -/
def one_level_tests_rename (x b s t p q : Nat)
    (fresh : [x,b,s,t,p,q].Nodup) :
    KDerivation (imp (oneLevelTransitiveCode x b s t) (oneLevelTransitiveCode x b p q)) := by
  have hx : [x,s,t,p,q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [oneLevelTransitiveCode x b s t]
  have hd : Context Γ (oneLevelTransitiveCode x b s t) := Context.head [] _
  have hOuter : Context Γ (transitiveCode x p q) :=
    .mp (Context.conjunctionLeft hd) (.closed (transitive_rename x s t p q hx))
  have hMembers : Context Γ (membersTransitiveCode x b p q) :=
    .mp (Context.conjunctionRight hd) (.closed (members_transitive_tests_rename x b s t p q fresh))
  exact Context.conjunctionIntro hOuter hMembers

theorem one_level_tests_rename_certificate (x b s t p q : Nat)
    (fresh : [x,b,s,t,p,q].Nodup) :
    theoremCode (certificate (one_level_tests_rename x b s t p q fresh)) =
      imp (oneLevelTransitiveCode x b s t) (oneLevelTransitiveCode x b p q) :=
  certificate_correct (one_level_tests_rename x b s t p q fresh)

end PASoundness.PAtoCompactCandidateAlphaTrans

#print axioms PASoundness.PAtoCompactCandidateAlphaTrans.members_transitive_tests_rename
#print axioms PASoundness.PAtoCompactCandidateAlphaTrans.one_level_tests_rename
#print axioms PASoundness.PAtoCompactCandidateAlphaTrans.one_level_tests_rename_certificate
