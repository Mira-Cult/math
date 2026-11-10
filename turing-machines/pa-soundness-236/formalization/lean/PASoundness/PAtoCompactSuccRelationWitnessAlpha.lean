import PASoundness.PAtoCompactSuccessorQuotientIntro
import PASoundness.PAtoCompactVacuousUniversalFresh
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.CompactFreshen

/-! Capture-safe relocation of the private quotient-successor witness to a
fresh low operand name. This is finite K proof data and does not assert any
successor-existence or semantic soundness property. -/
namespace PASoundness.PAtoCompactSuccRelationWitnessAlpha

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactSuccessorQuotientIntro
open PASoundness.PAtoCompactVacuousUniversalFresh PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Matrix of quotient successor with a chosen witness name. -/
def matrix (b a q w : Nat) : Formula :=
  andF (domainAt b a) (andF (domainAt b q) (andF (domainAt b w)
    (andF (Formula.all (b+10) (namedSuccessorBody a w (b+10))) (equivAt b w q))))

/-- Relocating the standard existential name changes only its witness
occurrences when the two operand names are below the private block. -/
theorem replace_body (b a q w : Nat) (ha : a < b+2) (hq : q < b+2) :
    replace (b+9) w (succBody b a q) = matrix b a q w := by
  unfold succBody matrix
  rw [replace_andF, replace_andF, replace_andF, replace_andF]
  rw [domain_replace_witness, domain_replace_witness, domain_replace_witness,
    raw_replace_witness b a w ha, equiv_replace_witness]
  simp [rename, show a ≠ b+9 by omega, show q ≠ b+9 by omega]

/-- A low fresh witness name is absent from every name of the original matrix. -/
theorem fresh_in_body (b a q w : Nat) (hw : w < b+2) (hwa : w ≠ a) (hwq : w ≠ q) :
    w ∉ (succBody b a q).names := by
  simp only [succBody, andF, CompactNamed.Formula.not, Formula.names,
    Finset.union_empty, Finset.mem_union, not_or]
  refine ⟨low_name_not_domain_names b a w hw hwa,
    low_name_not_domain_names b q w hw hwq,
    low_name_not_domain_names b (b+9) w hw (by omega), ?_, ?_⟩
  · simp [Formula.names, namedSuccessorBody, namedBoth, namedEither, hwa]
    omega
  · intro h
    have he := equivAt_name_bound b (b+9) q w h
    rcases he with he | he | he <;> omega

/-- Renaming the private existential witness is a capture-safe K proof
in both directions; no distinctness of the represented objects is required. -/
def rename_witness (b a q w : Nat) (ha : a < b+2) (hq : q < b+2)
    (hw : w < b+2) (hwa : w ≠ a) (hwq : w ≠ q) :
    ProofEquiv (succAt b a q) (.ex w (matrix b a q w)) := by
  have he := ProofEquiv.alphaExists (b+9) w (succBody b a q) (by omega)
    (succBody_witness_unbound b a q) (fresh_in_body b a q w hw hwa hwq)
  rw [replace_body b a q w ha hq] at he
  simpa only [succAt_shape, succBody] using he

end PASoundness.PAtoCompactSuccRelationWitnessAlpha

#print axioms PASoundness.PAtoCompactSuccRelationWitnessAlpha.rename_witness
