import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactFreshen

/-! Capture-safe alpha alignment of the reverse-preimage clause with the
second conjunct of the exact input-swapped bijection candidate. This neither
constructs an inverse graph nor proves order-isomorphism symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactReversePreimageAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def witnessBody (a b : Nat) : Formula :=
  conj (.member 1 a) (conj (graphFormula 7 a b)
    (.all 4 (.imp (conj (.member 1 4) (graphFormula 7 4 b)) (.equal 4 a))))

def reversePreimageFormula : Formula :=
  .all 2 (.imp (.member 0 2) (.ex 3 (witnessBody 3 2)))

/-- The second conjunct of the exact declared candidate bijection. -/
def candidateSecond : Formula := match bijectionFormula with
  | .imp (.imp _ (.imp second _)) _ => second
  | _ => .truth

/-- Simultaneously swap the free inputs using name 8, and change graph 6 to 7. -/
def swappedSecond : Formula :=
  replace 8 1 (replace 1 0 (replace 0 8 (replace 6 7 candidateSecond)))

/-- Alpha-equivalence between the transferred reverse preimage clause and the
second clause of the fixed swapped candidate. Name 8 avoids capture while
exchanging the quantifier labels 2 and 3. -/
def reverse_preimage_alpha : ProofEquiv reversePreimageFormula swappedSecond := by
  let b := witnessBody 3 2
  let b₁ := replace 3 8 b
  let f₁ : Formula := .imp (.member 0 2) (.ex 8 b₁)
  let b₂ := replace 2 3 b₁
  have h1 := ProofEquiv.alphaExists 3 8 b (by decide) (by decide) (by decide)
  have h1' := ProofEquiv.universal 2 (ProofEquiv.implication
    (ProofEquiv.refl (.member 0 2)) h1)
  have h2 := ProofEquiv.alphaAll 2 3 f₁ (by decide) (by decide) (by decide)
  have h3 := ProofEquiv.alphaExists 8 2 b₂ (by decide) (by decide) (by decide)
  have h3' := ProofEquiv.universal 3 (ProofEquiv.implication
    (ProofEquiv.refl (.member 0 3)) h3)
  have he1 : reversePreimageFormula = .all 2 (.imp (.member 0 2) (.ex 3 b)) := rfl
  have he2 : Formula.all 2 (.imp (.member 0 2) (.ex 8 b₁)) = .all 2 f₁ := rfl
  have he3 : replace 2 3 f₁ = .imp (.member 0 3) (.ex 8 b₂) := by decide
  have he4 : .all 3 (.imp (.member 0 3) (.ex 2 (replace 8 2 b₂))) = swappedSecond := by decide
  rw [he1]
  rw [he2] at h1'
  rw [he3] at h2
  rw [he4] at h3'
  exact h1'.trans (h2.trans h3')

def reverse_preimage_to_swapped_second : KDerivation
    (imp reversePreimageFormula.encode swappedSecond.encode) := reverse_preimage_alpha.forward

theorem reverse_preimage_to_swapped_second_certificate :
    theoremCode (certificate reverse_preimage_to_swapped_second) =
      imp reversePreimageFormula.encode swappedSecond.encode :=
  certificate_correct reverse_preimage_to_swapped_second

end PASoundness.PAtoCompactReversePreimageAlpha

#print axioms PASoundness.PAtoCompactReversePreimageAlpha.reverse_preimage_to_swapped_second
#print axioms PASoundness.PAtoCompactReversePreimageAlpha.reverse_preimage_to_swapped_second_certificate
