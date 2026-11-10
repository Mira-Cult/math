import PASoundness.PAtoCompactOrderIsoReverseInstance
import PASoundness.PAtoCompactIsoConditionalWrapper
import PASoundness.CompactFreshen

/-! Capture-safe alignment of the quantified reverse-order clause with the
exact order conjunct of the conditional-symmetry target. This proves a literal
K formula transformation, not inverse graph existence, symmetry, or a PA
interpretation. Compact code 1 remains the literal encoded falsum. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoReverseAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactIsoConditionalWrapper
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not
private def iff' (a b : Formula) : Formula := conj (a.imp b) (b.imp a)

/-- Pointwise reverse-order matrix: the four membership guards and two
reversed graph edges are exactly those in the source clause. -/
def body : Formula := .imp
  (conj (.member 1 3) (conj (.member 1 5) (conj (.member 0 2)
    (conj (.member 0 4) (conj (graphFormula 7 3 2) (graphFormula 7 5 4))))))
  (iff' (.member 5 3) (.member 4 2))

def quantified : Formula := .all 3 (.all 5 (.all 2 (.all 4 body)))

/-- Order conjunct inside the exact graph-renamed reverse target. -/
def matrixOrder : Formula := match reverseMatrix7 with
  | .imp (.imp _ (.imp second .bottom)) .bottom => second
  | _ => .truth

/-- The independently constructed named body is exactly the source numeric
matrix, including its nested compact conjunction encoding. -/
theorem source_body_code : body.encode =
    PASoundness.PAtoCompactOrderIsoReverseInstance.reverseMatrix := rfl

/-- Rename inner 2,4 through temporary 8,9, then free outer labels 3,5
and move them to 2,4, before restoring the inner labels as 3,5. Each
conversion is a literal K alpha-equivalence with syntactic freshness checks. -/
def order_alpha : ProofEquiv quantified matrixOrder := by
  let b := body
  let b₁ := replace 2 8 b
  let b₂ := replace 4 9 b₁
  let b₃ := replace 3 2 b₂
  let b₄ := replace 5 4 b₃
  let b₅ := replace 8 3 b₄
  let b₆ := replace 9 5 b₅
  have h1 := ProofEquiv.universal 3 (ProofEquiv.universal 5
    (ProofEquiv.alphaAll 2 8 (.all 4 b) (by decide) (by decide) (by decide)))
  have e1 : replace 2 8 (.all 4 b) = .all 4 b₁ := by decide
  rw [e1] at h1
  have h2 := ProofEquiv.universal 3 (ProofEquiv.universal 5 (ProofEquiv.universal 8
    (ProofEquiv.alphaAll 4 9 b₁ (by decide) (by decide) (by decide))))
  have h3 := ProofEquiv.alphaAll 3 2 (.all 5 (.all 8 (.all 9 b₂)))
    (by decide) (by decide) (by decide)
  have e3 : replace 3 2 (.all 5 (.all 8 (.all 9 b₂))) =
      .all 5 (.all 8 (.all 9 b₃)) := by decide
  rw [e3] at h3
  have h4 := ProofEquiv.universal 2 (ProofEquiv.alphaAll 5 4 (.all 8 (.all 9 b₃))
    (by decide) (by decide) (by decide))
  have e4 : replace 5 4 (.all 8 (.all 9 b₃)) = .all 8 (.all 9 b₄) := by decide
  rw [e4] at h4
  have h5 := ProofEquiv.universal 2 (ProofEquiv.universal 4
    (ProofEquiv.alphaAll 8 3 (.all 9 b₄) (by decide) (by decide) (by decide)))
  have e5 : replace 8 3 (.all 9 b₄) = .all 9 b₅ := by decide
  rw [e5] at h5
  have h6 := ProofEquiv.universal 2 (ProofEquiv.universal 4 (ProofEquiv.universal 3
    (ProofEquiv.alphaAll 9 5 b₅ (by decide) (by decide) (by decide))))
  have e6 : replace 9 5 b₅ = b₆ := by decide
  rw [e6] at h6
  have et : .all 2 (.all 4 (.all 3 (.all 5 b₆))) = matrixOrder := by decide
  rw [et] at h6
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-- Explicit K derivation for the requested direction. -/
def align_order : KDerivation (imp quantified.encode matrixOrder.encode) := order_alpha.forward

theorem align_order_certificate :
    theoremCode (certificate align_order) = imp quantified.encode matrixOrder.encode :=
  certificate_correct align_order

/-- Exact numeric interface for the quantified reverse-order construction. -/
def align_order_numeric : KDerivation
    (imp (allCode 3 (allCode 5 (allCode 2 (allCode 4
      PASoundness.PAtoCompactOrderIsoReverseInstance.reverseMatrix)))) matrixOrder.encode) :=
  align_order

theorem align_order_numeric_certificate :
    theoremCode (certificate align_order_numeric) =
      imp (allCode 3 (allCode 5 (allCode 2 (allCode 4
        PASoundness.PAtoCompactOrderIsoReverseInstance.reverseMatrix)))) matrixOrder.encode :=
  certificate_correct align_order_numeric

end PASoundness.PAtoCompactOrderIsoReverseAlpha

#print axioms PASoundness.PAtoCompactOrderIsoReverseAlpha.align_order
#print axioms PASoundness.PAtoCompactOrderIsoReverseAlpha.align_order_certificate
#print axioms PASoundness.PAtoCompactOrderIsoReverseAlpha.align_order_numeric
#print axioms PASoundness.PAtoCompactOrderIsoReverseAlpha.align_order_numeric_certificate
