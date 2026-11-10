import PASoundness.PAtoCompactTermZeroGuarded
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactFreeNames

/-! Lift a supplied finite-K addition-output relation proof through an actual
addition-node graph. Both child candidate predicates are projected from the
same original child-graph witnesses; no functionality or recursive output law
is assumed. The addition relation proof remains an explicit input. -/
namespace PASoundness.PAtoCompactAdditionOutputGraphConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- An explicit operation-level finite K proof. Its source relation,
source-output, target-output, right-child and left-child candidate predicates
and output isomorphism all remain object-level antecedents. -/
def RelationOutput (b q r : Nat) : Type := KDerivation
  (imp (addAt b b (b+1) q).encode
    (imp (domainAt b q).encode (imp (domainAt b r).encode
      (imp (domainAt b (b+1)).encode (imp (domainAt b b).encode
        (imp (equivAt b q r).encode (addAt b b (b+1) r).encode))))))

/-- A source addition graph, target candidate and output isomorphism imply a
target graph, provided the explicitly supplied operation proof. The same
original left/right child witnesses are used in the target; source-output and
both child candidates come from their actual graphs. Displayed inequalities
are name-allocation bounds, not inequalities of denoted values. -/
noncomputable def addition_output_lift {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ (binaryTerm true t u).varFinset, v a < b)
    (operation : RelationOutput b q r) :
    KDerivation (imp (domainAt b r).encode
      (imp (termGraph v (binaryTerm true t u) q b).encode
        (imp (equivAt b q r).encode (termGraph v (binaryTerm true t u) r b).encode))) := by
  let G := andF (domainAt b q) (andF (domainAt b r) (equivAt b q r))
  let L := termGraph v t b (b+64)
  let R := termGraph v u (b+1) (b+64+termCost t)
  let M := andF L (andF R (binaryRel true b b (b+1) q))
  let T := termGraph v (binaryTerm true t u) r b
  have hG (k : Nat) (hk : b ≤ k) : k ∉ G.free := by
    intro h
    simp only [G, andF_free, Finset.mem_union] at h
    rcases h with hdq | hdr | he
    · have hh := domainAt_free b q hdq
      simp only [Finset.mem_singleton] at hh
      omega
    · have hh := domainAt_free b r hdr
      simp only [Finset.mem_singleton] at hh
      omega
    · have hh := equivAt_free b q r he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh <;> omega
  have hT (k : Nat) (hk : b ≤ k) : k ∉ T.free := by
    intro h
    have hh := termGraph_free_subset v (binaryTerm true t u) r b h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hh
    rcases hh with ⟨a, ha, he⟩ | he
    · have ha' := hv a ha
      omega
    · omega
  have introGraph := binary_from_witness v true t u b r
  have hpoint : KDerivation (imp G.encode (imp M.encode T.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode,G.encode]
    have hg0 : Context Γ G.encode := .hypothesis (by simp [Γ])
    have hm0 : Context Γ M.encode := .head _ _
    have hg : Context Γ (both (domainAt b q).encode
        (both (domainAt b r).encode (equivAt b q r).encode)) := by
      simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg0
    have hm : Context Γ (both L.encode (both R.encode (binaryRel true b b (b+1) q).encode)) := by
      simpa [M, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hm0
    have hdq := Context.conjunctionLeft hg
    have hdr := Context.conjunctionLeft (Context.conjunctionRight hg)
    have he := Context.conjunctionRight (Context.conjunctionRight hg)
    have hl := Context.conjunctionLeft hm
    have hr' := Context.conjunctionLeft (Context.conjunctionRight hm)
    have hrel := Context.conjunctionRight (Context.conjunctionRight hm)
    have hdL : Context Γ (domainAt (b+64) b).encode :=
      .mp hl (.closed (termGraph_domain v t b (b+64)))
    have hdR : Context Γ (domainAt (b+64+termCost t) (b+1)).encode :=
      .mp hr' (.closed (termGraph_domain v u (b+1) (b+64+termCost t)))
    have dx : Context Γ (domainAt b b).encode :=
      .mp hdL (.closed (domainAt_transport (b+64) b b (by omega) (by omega)))
    have dy : Context Γ (domainAt b (b+1)).encode :=
      .mp hdR (.closed (domainAt_transport (b+64+termCost t) b (b+1) (by omega) (by omega)))
    have hrel0 : Context Γ (addAt b b (b+1) q).encode := by
      simpa [binaryRel] using hrel
    have hrel1 : Context Γ (addAt b b (b+1) r).encode :=
      .mp he (.mp dx (.mp dy (.mp hdr (.mp hdq (.mp hrel0 (.closed operation))))))
    have hrel' : Context Γ (binaryRel true b b (b+1) r).encode := by
      simpa [binaryRel] using hrel1
    exact .mp hrel' (.mp hr' (.mp hl (.mp hdr (.closed introGraph))))
  have inner := guarded_exists_left (b+1) G.encode M.encode T.encode
    (free_vacuity (b+1) G (hG (b+1) (by omega)))
    (free_vacuity (b+1) T (hT (b+1) (by omega))) hpoint
  have outer := guarded_exists_left b G.encode (existsCode (b+1) M.encode) T.encode
    (free_vacuity b G (hG b (by omega)))
    (free_vacuity b T (hT b (by omega))) inner
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt b q r).encode,(termGraph v (binaryTerm true t u) q b).encode,(domainAt b r).encode]
  have he : Context Γ (equivAt b q r).encode := .head _ _
  have hs : Context Γ (termGraph v (binaryTerm true t u) q b).encode := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt b r).encode := .hypothesis (by simp [Γ])
  have hs' : Context Γ (both (domainAt b q).encode (existsCode b (existsCode (b+1) M.encode))) := by
    simpa [binaryTerm, binaryRel, termGraph, M, L, R, andF,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hs
  have hg : Context Γ G.encode := by
    simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hs') (Context.conjunctionIntro hd he)
  exact .mp (Context.conjunctionRight hs') (.mp hg (.closed outer))

theorem addition_output_lift_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b q r : Nat) (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ (binaryTerm true t u).varFinset, v a < b)
    (operation : RelationOutput b q r) :
    theoremCode (certificate (addition_output_lift v t u b q r hq hr hv operation)) =
      imp (domainAt b r).encode (imp (termGraph v (binaryTerm true t u) q b).encode
        (imp (equivAt b q r).encode (termGraph v (binaryTerm true t u) r b).encode)) :=
  certificate_correct _
end PASoundness.PAtoCompactAdditionOutputGraphConditional

#print axioms PASoundness.PAtoCompactAdditionOutputGraphConditional.addition_output_lift
#print axioms PASoundness.PAtoCompactAdditionOutputGraphConditional.addition_output_lift_certificate
