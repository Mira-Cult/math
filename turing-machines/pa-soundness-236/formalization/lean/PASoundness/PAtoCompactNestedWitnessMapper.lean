import PASoundness.CompactNamed

/-! A generic nested-existential K proof transformer.  The proof takes literal
K vacuity derivations at all three binders and a literal pointwise K step. It
retains the same outer, middle and inner witnesses and adds the pointwise
conclusion to the inner witness body.  No semantic soundness, existence,
isomorphism or arithmetic property is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactNestedWitnessMapper
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Given the three displayed context-vacuity K proofs, retain nested
witnesses while appending the conclusion of the pointwise K proof at the
innermost witness. The binders may be arbitrary; the vacuity proofs carry
all required binding restrictions. -/
def map_nested_witnesses (x y z H B P G Q : Nat)
    (hH : KDerivation (imp H (allCode x H)))
    (hHB : KDerivation (imp (both H B) (allCode y (both H B))))
    (hHBP : KDerivation (imp (both (both H B) P) (allCode z (both (both H B) P))))
    (step : KDerivation (imp H (imp B (imp P (imp G Q))))) :
    KDerivation (imp H
      (imp (existsCode x (both B (existsCode y (both P (existsCode z G)))))
        (existsCode x (both B (existsCode y (both P (existsCode z (both G Q)))))))) := by
  let E2 := both (both H B) P
  have hz : KDerivation (imp E2 (imp G (both G Q))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [G,E2]
    have hg : Context Γ G := .head _ _
    have he : Context Γ E2 := .under (.head [] E2) _
    have hp : Context Γ P := Context.conjunctionRight he
    have hhb : Context Γ (both H B) := Context.conjunctionLeft he
    have hh : Context Γ H := Context.conjunctionLeft hhb
    have hb : Context Γ B := Context.conjunctionRight hhb
    have hq : Context Γ Q := .mp hg (.mp hp (.mp hb (.mp hh (.closed step))))
    exact Context.conjunctionIntro hg hq
  have hz' := conditionalExistsCongr z hHBP hz
  let E1 := both H B
  have hy : KDerivation (imp E1
      (imp (both P (existsCode z G)) (both P (existsCode z (both G Q))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [both P (existsCode z G),E1]
    have hpz : Context Γ (both P (existsCode z G)) := .head _ _
    have he : Context Γ E1 := .under (.head [] E1) _
    have hp : Context Γ P := Context.conjunctionLeft hpz
    have hz0 : Context Γ (existsCode z G) := Context.conjunctionRight hpz
    have he2 : Context Γ E2 := Context.conjunctionIntro he hp
    have hz1 : Context Γ (existsCode z (both G Q)) := .mp hz0 (.mp he2 (.closed hz'))
    exact Context.conjunctionIntro hp hz1
  have hy' := conditionalExistsCongr y hHB hy
  have hx : KDerivation (imp H
      (imp (both B (existsCode y (both P (existsCode z G))))
        (both B (existsCode y (both P (existsCode z (both G Q))))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [both B (existsCode y (both P (existsCode z G))),H]
    have hbz : Context Γ (both B (existsCode y (both P (existsCode z G)))) := .head _ _
    have hh : Context Γ H := .under (.head [] H) _
    have hb : Context Γ B := Context.conjunctionLeft hbz
    have hy0 : Context Γ (existsCode y (both P (existsCode z G))) := Context.conjunctionRight hbz
    have he1 : Context Γ E1 := Context.conjunctionIntro hh hb
    have hy1 : Context Γ (existsCode y (both P (existsCode z (both G Q)))) :=
      .mp hy0 (.mp he1 (.closed hy'))
    exact Context.conjunctionIntro hb hy1
  exact conditionalExistsCongr x hH hx

theorem map_nested_witnesses_certificate (x y z H B P G Q : Nat)
    (hH : KDerivation (imp H (allCode x H)))
    (hHB : KDerivation (imp (both H B) (allCode y (both H B))))
    (hHBP : KDerivation (imp (both (both H B) P) (allCode z (both (both H B) P))))
    (step : KDerivation (imp H (imp B (imp P (imp G Q))))) :
    theoremCode (certificate (map_nested_witnesses x y z H B P G Q hH hHB hHBP step)) =
      imp H (imp (existsCode x (both B (existsCode y (both P (existsCode z G)))))
        (existsCode x (both B (existsCode y (both P (existsCode z (both G Q))))))) :=
  certificate_correct (map_nested_witnesses x y z H B P G Q hH hHB hHBP step)
end PASoundness.PAtoCompactNestedWitnessMapper
#print axioms PASoundness.PAtoCompactNestedWitnessMapper.map_nested_witnesses
#print axioms PASoundness.PAtoCompactNestedWitnessMapper.map_nested_witnesses_certificate
