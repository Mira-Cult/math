import PASoundness.PAtoCompactSuccVariableFunctionalityConditional
import PASoundness.PAtoCompactSuccCongruenceWitnessLift

/-! Finite K functionality of the successor-of-variable term graph. The
compatibility input is supplied by the independently constructed quotient
successor congruence theorem and private-block transports. -/
namespace PASoundness.PAtoCompactSuccVariableFunctionalityClosed

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactSuccCongruenceWitnessLift
open PASoundness.PAtoCompactSuccVariableFunctionalityConditional

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Two outputs of the translated successor of a variable are equivalent,
under the explicit candidate guard for that variable. The source name and
both outputs are below the allocator; outputs and source name may alias. -/
noncomputable def successor_variable_functional {α : Type} [DecidableEq α]
    (v : α → Nat) (a : α) (b p q : Nat)
    (ha : v a < b) (hp : p < b) (hq : q < b) :
    KDerivation (imp (domainAt b (v a)).encode
      (imp (termGraph v (.func .succ ![.var a]) p b).encode
        (imp (termGraph v (.func .succ ![.var a]) q b).encode (equivAt b p q).encode))) := by
  let c := b + 1
  let d := c + 64
  have hs1 := (succAt_base_alpha b d b p (by omega) (by omega) (by dsimp [d,c]; omega) (by dsimp [d,c]; omega)).forward
  have hs2 := (succAt_base_alpha c d c q (by omega) (by dsimp [c]; omega) (by dsimp [d]; omega) (by dsimp [d,c]; omega)).forward
  have ho := (equivAt_base_alpha d b p q (by dsimp [d,c]; omega) (by dsimp [d,c]; omega) (by omega) (by omega)).forward
  have hcon := successor_congruence d b c p q (by dsimp [d,c]; omega)
    (by dsimp [d]; omega) (by dsimp [d,c]; omega) (by dsimp [d,c]; omega)
  have hnext : KDerivation (imp (domainAt b (v a)).encode
      (imp (equivAt d b c).encode (imp (succAt b b p).encode
        (imp (succAt c c q).encode (equivAt b p q).encode)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let E := (equivAt d b c).encode
    let S := (succAt b b p).encode
    let T := (succAt c c q).encode
    let G := (domainAt b (v a)).encode
    let Γ := [T,S,E,G]
    have he : Context Γ E := .hypothesis (by simp [Γ])
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have ht : Context Γ T := .head _ _
    have hs' := Context.mp hs (Context.closed hs1)
    have ht' := Context.mp ht (Context.closed hs2)
    exact .mp (.mp ht' (.mp hs' (.mp he (.closed hcon)))) (.closed ho)
  exact PAtoCompactSuccVariableFunctionalityConditional.successor_variable_functional
    v a b c p q b (by dsimp [c]; omega) ha hp hq
    (by simpa only [d] using hnext)

end PASoundness.PAtoCompactSuccVariableFunctionalityClosed

#print axioms PASoundness.PAtoCompactSuccVariableFunctionalityClosed.successor_variable_functional
