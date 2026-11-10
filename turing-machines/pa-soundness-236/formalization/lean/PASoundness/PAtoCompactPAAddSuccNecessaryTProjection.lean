import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactQuantifiers

/-! A finite K projection from an addition term graph to its left child graph.
The allocation-side bound is explicit; this does not prove either graph exists. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccNecessaryTProjection
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity

/-- An addition graph entails the existence of its left child graph at the
actual generated witness name and child base. The variable-name map need not
be injective, and there is no assumption of addition functionality. -/
def addition_left_child {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (out b : Nat)
    (ht : ∀ a ∈ t.varFinset, v a < b) :
    KDerivation (imp (termGraph v (.func .add ![t,u]) out b).encode
      (existsCode b (termGraph v t b (b+64)).encode)) := by
  let T := termGraph v t b (b+64)
  let U := termGraph v u (b+1) (b+64+termCost t)
  let R := addAt b b (b+1) out
  let M := andF T (andF U R)
  have hfree : b+1 ∉ T.free := by
    intro h
    have hs := termGraph_free_subset v t b (b+64) h
    rcases Finset.mem_union.mp hs with hi | hi
    · obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hi
      have hh := ht a ha
      omega
    · have hh := Finset.mem_singleton.mp hi
      omega
  have hv := free_vacuity (b+1) T hfree
  have hp : KDerivation (imp M.encode T.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [M.encode]
    have h : Context Γ (both T.encode (both U.encode R.encode)) := by
      have hh := Context.head [] M.encode
      simpa [Γ, M, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hh
    exact Context.conjunctionLeft h
  have hinner : KDerivation (imp (existsCode (b+1) M.encode) T.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h := Context.head [] (existsCode (b+1) M.encode)
    exact Context.existsElim hv (.closed (.generalize (b+1) hp)) h
  have houter := existsCongr b hinner
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(termGraph v (.func .add ![t,u]) out b).encode]
  have hg : Context Γ (termGraph v (.func .add ![t,u]) out b).encode := .head _ _
  have hb : Context Γ (existsCode b (existsCode (b+1) M.encode)) := by
    have hconj : Context Γ (both (domainAt b out).encode
        (existsCode b (existsCode (b+1) M.encode))) := by
      simpa [Γ, termGraph, T, U, R, M, andF, CompactNamed.Formula.not,
        Formula.encode, both, neg, existsCode] using hg
    exact Context.conjunctionRight hconj
  exact .mp hb (.closed houter)

theorem addition_left_child_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (out b : Nat)
    (ht : ∀ a ∈ t.varFinset, v a < b) :
    theoremCode (certificate (addition_left_child v t u out b ht)) =
      imp (termGraph v (.func .add ![t,u]) out b).encode
        (existsCode b (termGraph v t b (b+64)).encode) := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccNecessaryTProjection
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryTProjection.addition_left_child
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryTProjection.addition_left_child_certificate
