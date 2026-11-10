import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactFreshen

/-! Capture-safe alpha alignment for the reversed image clause. The fixed
quotient candidate is unchanged. This supplies equivalence of two literal K
formula codes, not graph inversion, inverse existence, or whole symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInverseAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def witnessBody (a b : Nat) : Formula :=
  conj (.member 0 a) (conj (graphFormula 7 b a)
    (.all 4 (.imp (conj (.member 0 4) (graphFormula 7 b 4)) (.equal 4 a))))

def reverseImageFormula : Formula :=
  .all 3 (.imp (.member 1 3) (.ex 2 (witnessBody 2 3)))

/-- The first conjunct of the exact declared candidate bijection. -/
def candidateFirst : Formula := match bijectionFormula with
  | .imp (.imp first _) _ => first
  | _ => .truth

/-- Rename the two free input names simultaneously using fresh name 8, and
replace graph name 6 by 7. The candidate's bound names are not renamed. -/
def swappedFirst : Formula :=
  replace 8 1 (replace 1 0 (replace 0 8 (replace 6 7 candidateFirst)))

/-- The reversed image clause is bidirectionally K-equivalent to the first
clause of the exact candidate after swapping inputs and the graph name. The
three alpha conversions use temporary name 8 to avoid capture between the
original binders 2 and 3. -/
def reverse_image_alpha : ProofEquiv reverseImageFormula swappedFirst := by
  let b := witnessBody 2 3
  let b₁ := replace 2 8 b
  let f₁ : Formula := .imp (.member 1 3) (.ex 8 b₁)
  let b₂ := replace 3 2 b₁
  have h1 := ProofEquiv.alphaExists 2 8 b (by decide) (by decide) (by decide)
  have h1' := ProofEquiv.universal 3 (ProofEquiv.implication
    (ProofEquiv.refl (.member 1 3)) h1)
  have h2 := ProofEquiv.alphaAll 3 2 f₁ (by decide) (by decide) (by decide)
  have h3 := ProofEquiv.alphaExists 8 3 b₂ (by decide) (by decide) (by decide)
  have h3' := ProofEquiv.universal 2 (ProofEquiv.implication
    (ProofEquiv.refl (.member 1 2)) h3)
  have he1 : reverseImageFormula = .all 3 (.imp (.member 1 3) (.ex 2 b)) := rfl
  have he2 : Formula.all 3 (.imp (.member 1 3) (.ex 8 b₁)) = .all 3 f₁ := rfl
  have he3 : replace 3 2 f₁ = .imp (.member 1 2) (.ex 8 b₂) := by decide
  have he4 : .all 2 (.imp (.member 1 2) (.ex 3 (replace 8 3 b₂))) = swappedFirst := by decide
  rw [he1]
  rw [he2] at h1'
  rw [he3] at h2
  rw [he4] at h3'
  exact h1'.trans (h2.trans h3')

/-- One requested direction as explicit finite K derivation data. -/
def reverse_image_to_swapped_first : KDerivation
    (imp reverseImageFormula.encode swappedFirst.encode) := reverse_image_alpha.forward

theorem reverse_image_to_swapped_first_certificate :
    theoremCode (certificate reverse_image_to_swapped_first) =
      imp reverseImageFormula.encode swappedFirst.encode :=
  certificate_correct reverse_image_to_swapped_first

end PASoundness.PAtoCompactInverseAlpha

#print axioms PASoundness.PAtoCompactInverseAlpha.reverse_image_to_swapped_first
#print axioms PASoundness.PAtoCompactInverseAlpha.reverse_image_to_swapped_first_certificate
