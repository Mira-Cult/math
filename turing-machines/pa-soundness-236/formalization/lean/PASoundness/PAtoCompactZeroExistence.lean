import PASoundness.PAtoCompactZeroSuccessor

/-! Constructive selector-8 witness for the code-one zero graph. This establishes
existence, not uniqueness or a complete PA-domain interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactZeroExistence
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor

/-- Exact selector-8 body at predicate/witness code 1. Code 1 is literally
`member 0 0`; its use as a false value requires an appropriate interpretation. -/
def zeroWitnessBody (a b : Nat) : Nat :=
  both (allCode b (both
      (imp (member a b) (imp 1 (member 1 b)))
      (imp (member 1 b) 1)))
    (imp 1 (member 1 b))

/-- Selector 8 produces this exact body when its input and point names do not
collide with its predicate/witness name 1. -/
def zero_selector_witness (a b : Nat) (ha : 1 ≠ a) (hb : 1 ≠ b) :
    KDerivation (existsCode 1 (zeroWitnessBody a b)) := by
  have h := KDerivation.axiom (⟨8, by decide⟩ : Fin 9) a b 1 0
  simp only [axiomCode, show ¬ (1 = a ∨ 1 = b) from not_or_intro ha hb, ↓reduceIte] at h
  exact Context.closeEmpty (Context.conjunctionLeft (.closed h))

/-- The selector witness satisfies the stated compact zero graph, by literal
K projection and quantifier congruence. No semantic soundness is used. -/
def zero_graph_exists (b : Nat) (hb : b ≠ 1) :
    KDerivation (existsCode 1 (zeroCode 1 b)) := by
  let a := 0
  let inner := both (imp (member a b) (imp 1 (member 1 b))) (imp (member 1 b) 1)
  have hinner : KDerivation (imp inner (neg (member 1 b))) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.conjunctionRight (Context.head [] inner)
  have hbody : KDerivation (imp (zeroWitnessBody a b) (zeroCode 1 b)) := by
    have hp : KDerivation (imp (zeroWitnessBody a b) (allCode b inner)) := by
      apply Context.closeEmpty
      apply Context.deduction
      exact Context.conjunctionLeft (Context.head [] (zeroWitnessBody a b))
    exact compose hp (allCongr b hinner)
  exact .mp (zero_selector_witness a b (by decide) (Ne.symm hb)) (existsCongr 1 hbody)

/-- A fully explicit instance uses witness variable 1 and test variable 2. -/
def zero_graph_exists_closed : KDerivation (existsCode 1 (zeroCode 1 2)) :=
  zero_graph_exists 2 (by decide)

theorem zero_graph_exists_certificate (b : Nat) (hb : b ≠ 1) :
    theoremCode (certificate (zero_graph_exists b hb)) = existsCode 1 (zeroCode 1 b) :=
  certificate_correct (zero_graph_exists b hb)

/-- On the standard HF/Nat code model, code 1 is false and the same zero
graph means value 0. This is separate from the constructive K proof above. -/
theorem zero_graph_standard_meaning (b : Nat) (ρ : CompactMatrix.Environment) (hb : b ≠ 1) :
    (CompactMatrix.decode (zeroCode 1 b)).Realize ρ ↔ ρ 1 = 0 :=
  zeroCode_realize 1 b ρ (Ne.symm hb)

end PASoundness.PAtoCompactZeroExistence
