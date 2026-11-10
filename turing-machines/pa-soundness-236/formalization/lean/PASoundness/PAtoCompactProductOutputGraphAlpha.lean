import PASoundness.PAtoCompactProductOutputAdjoinInvariant9
import PASoundness.CompactFreshen

/-! A constructive, scoped alpha conversion for the target graph witness.
The path payload also binds name 9, so first rename each eligible inner binder
9 to 65, keeping free graph occurrences untouched. This produces finite K
proofs and does not appeal to semantic soundness. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputGraphAlpha

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputAdjoinInvariant9

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename an inner binder 9 to 65 without changing free occurrences of 9. -/
def shift9 : Formula → Formula
  | .truth => .truth
  | .bottom => .bottom
  | .member a b => .member a b
  | .equal a b => .equal a b
  | .imp a b => .imp (shift9 a) (shift9 b)
  | .all n a => if n = 9 then .all 65 (replace 9 65 a) else .all n (shift9 a)
  | .ex n a => if n = 9 then .ex 65 (replace 9 65 a) else .ex n (shift9 a)

/-- The fixed conversion is applied only where its local alpha premises hold. -/
def shiftSafe : Formula → Bool
  | .truth | .bottom | .member _ _ | .equal _ _ => true
  | .imp a b => shiftSafe a && shiftSafe b
  | .all n a | .ex n a =>
      if n = 9 then decide (9 ∉ a.binders ∧ 65 ∉ a.names) else shiftSafe a

/-- Structural K alpha proof for the displayed scoped transformation. -/
noncomputable def shift_equiv (f : Formula) (h : shiftSafe f = true) : ProofEquiv f (shift9 f) := by
  induction f with
  | truth => exact ProofEquiv.refl .truth
  | bottom => exact ProofEquiv.refl .bottom
  | member a b => exact ProofEquiv.refl (.member a b)
  | equal a b => exact ProofEquiv.refl (.equal a b)
  | imp a b ia ib =>
      have hab : shiftSafe a = true ∧ shiftSafe b = true := by simpa [shiftSafe] using h
      exact ProofEquiv.implication (ia hab.1) (ib hab.2)
  | all n a ia =>
      by_cases hn : n = 9
      · subst n
        have hs : 9 ∉ a.binders ∧ 65 ∉ a.names := by simpa [shiftSafe] using h
        simpa [shift9] using ProofEquiv.alphaAll 9 65 a (by decide) hs.1 hs.2
      · have hs : shiftSafe a = true := by simpa [shiftSafe, hn] using h
        simpa [shift9, hn] using ProofEquiv.universal n (ia hs)
  | ex n a ia =>
      by_cases hn : n = 9
      · subst n
        have hs : 9 ∉ a.binders ∧ 65 ∉ a.names := by simpa [shiftSafe] using h
        simpa [shift9] using ProofEquiv.alphaExists 9 65 a (by decide) hs.1 hs.2
      · have hs : shiftSafe a = true := by simpa [shiftSafe, hn] using h
        simpa [shift9, hn] using ProofEquiv.existential n (ia hs)

theorem original_safe : shiftSafe partialInvariant = true := by decide
theorem next_safe : shiftSafe nextInvariant9 = true := by decide
theorem shifted_alignment : shift9 nextInvariant9 = replace 58 9 (shift9 partialInvariant) := by decide
theorem graph_name_fresh : 9 ∉ (shift9 partialInvariant).names := by decide
theorem original_graph_unbound : 58 ∉ (shift9 partialInvariant).binders := by decide

/-- Convert a graph-9 witness into the required existential graph-58 witness.
The interior binder is restored after the graph witness has been renamed. -/
noncomputable def graph_existential_alpha : KDerivation (imp (existsCode 9 nextInvariant9.encode)
    (existsCode 58 partialInvariant.encode)) := by
  have hf := existsCongr 9 (shift_equiv nextInvariant9 next_safe).forward
  rw [shifted_alignment] at hf
  have ha := (existentialAlpha 58 9 (shift9 partialInvariant) (by decide)
    original_graph_unbound graph_name_fresh).2
  have hb := existsCongr 58 (shift_equiv partialInvariant original_safe).backward
  exact compose hf (compose ha hb)

theorem graph_existential_alpha_certificate : theoremCode (certificate graph_existential_alpha) =
    imp (existsCode 9 nextInvariant9.encode) (existsCode 58 partialInvariant.encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputGraphAlpha

#print axioms PASoundness.PAtoCompactProductOutputGraphAlpha.shift_equiv
#print axioms PASoundness.PAtoCompactProductOutputGraphAlpha.graph_existential_alpha
#print axioms PASoundness.PAtoCompactProductOutputGraphAlpha.graph_existential_alpha_certificate
