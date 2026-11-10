import PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional
import PASoundness.PAtoCompactVariableGraphLaws

/-! Specialize successor graph functionality to the graph of a source
variable. The remaining quotient-successor compatibility is an explicit K
proof input. No quotient operation compatibility is claimed here. -/
namespace PASoundness.PAtoCompactSuccVariableFunctionalityConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactVariableGraphLaws
open PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The child graphs of one variable have equivalent outputs, even when
allocated in two distinct blocks. -/
noncomputable def variable_child_functional {α : Type} [DecidableEq α]
    (v : α → Nat) (a : α) (b c : Nat) (hbc : b < c) (ha : v a < b) :
    KDerivation (imp (domainAt b (v a)).encode
      (imp (termGraph v (.var a) b (b+64)).encode
        (imp (termGraph v (.var a) c (c+64)).encode (equivAt (c+64) b c).encode))) := by
  have hd := domainAt_transport b (c+64) (v a) (by omega) (by omega)
  have ht := (termGraph_base_transport v (.var a) (b+64) (c+64) b
    (by omega) (by omega) (by simp [Term.varFinset]; omega)
    (by simp [Term.varFinset]; omega)).1
  have hf := variable_functional v a (c+64) b c (by omega) (by omega) (by omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (domainAt b (v a)).encode
  let A := (termGraph v (.var a) b (b+64)).encode
  let B := (termGraph v (.var a) c (c+64)).encode
  let Γ := [B,A,G]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hB : Context Γ B := .head _ _
  exact .mp hB (.mp (.mp hA (.closed ht)) (.mp (.mp hg (.closed hd)) (.closed hf)))

/-- Functionality of successor-variable graphs at a common base, conditional
only on a finite K proof that quotient successor respects equivalence. -/
noncomputable def successor_variable_functional {α : Type} [DecidableEq α]
    (v : α → Nat) (a : α) (b c p q f : Nat)
    (hbc : b < c) (ha : v a < b) (hp : p < b) (hq : q < b)
    (next : KDerivation (imp (domainAt b (v a)).encode
      (imp (equivAt (c+64) b c).encode (imp (succAt b b p).encode
        (imp (succAt c c q).encode (equivAt f p q).encode))))) :
    KDerivation (imp (domainAt b (v a)).encode
      (imp (termGraph v (.func .succ ![.var a]) p b).encode
        (imp (termGraph v (.func .succ ![.var a]) q b).encode (equivAt f p q).encode))) := by
  have hgb : b ∉ (domainAt b (v a)).free := by
    intro h
    have hh := domainAt_free b (v a) h
    simp only [Finset.mem_singleton] at hh
    omega
  have hgc : c ∉ (domainAt b (v a)).free := by
    intro h
    have hh := domainAt_free b (v a) h
    simp only [Finset.mem_singleton] at hh
    omega
  apply successor_functionality_same_base v (.var a) b c p q (c+64) f
    (domainAt b (v a)) hbc hp hq
  · simpa [Term.varFinset] using ha
  · exact hgb
  · exact hgc
  · exact variable_child_functional v a b c hbc ha
  · exact next

end PASoundness.PAtoCompactSuccVariableFunctionalityConditional

#print axioms PASoundness.PAtoCompactSuccVariableFunctionalityConditional.variable_child_functional
#print axioms PASoundness.PAtoCompactSuccVariableFunctionalityConditional.successor_variable_functional
