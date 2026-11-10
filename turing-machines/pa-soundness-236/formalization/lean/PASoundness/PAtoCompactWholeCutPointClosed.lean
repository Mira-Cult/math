import PASoundness.PAtoCompactWholeCutZeroTransfer
import PASoundness.PAtoCompactWholeCutLeftTransport
import PASoundness.PAtoCompactWholeCutWitnessElimination

/-! Close the fixed-label equal-cut point from the actual source witnesses,
then eliminate that same pair of witnesses. The member-cut branch remains
separate; this is not an addition output-transport theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactWholeCutPointClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactWholeCutWitnessElimination
open PASoundness.PAtoCompactWholeCutZeroTransfer PASoundness.PAtoCompactWholeCutLeftTransport
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact literal suffix encoding is the filter used by the zero lemma. -/
private theorem suffix_code : PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode =
    filterGraph 32 34 35 (neg (member 33 35)) := by rfl

/-- Under one actual equal cut and its suffix, with the original left- and
right-to-segment equivalences, the candidate guard on the left input and
old-to-new output equivalence yield the target addition relation. -/
noncomputable def whole_cut_point : KDerivation (imp (equal 33 32)
    (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
      (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
        (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode)))) := by
  change KDerivation (imp (equal 33 32)
    (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
      (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
        (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode
          (imp (domainAt 100 30).encode
            (imp (equivAt 100 32 8).encode (addAt 100 30 31 8).encode))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt 100 32 8).encode, (domainAt 100 30).encode,
    (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode,
    PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode,
    (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode, equal 33 32]
  have hout : Context Γ (equivAt 100 32 8).encode := .head _ _
  have hd : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hr : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode :=
    .hypothesis (by simp [Γ])
  have hs : Context Γ PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode :=
    .hypothesis (by simp [Γ])
  have hl : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode :=
    .hypothesis (by simp [Γ])
  have he : Context Γ (equal 33 32) := .hypothesis (by simp [Γ])
  have hf : Context Γ (filterGraph 32 34 35 (neg (member 33 35))) := by
    simpa only [suffix_code] using hs
  have hz : Context Γ (zeroCode 31 36) :=
    .mp hr (.mp hf (.mp he (.closed whole_cut_right_zero)))
  exact .mp hz (.mp hout (.mp hd (.mp hl (.mp he (.closed whole_cut_left_transport)))))

/-- The actual equal-cut and suffix witnesses can be existentially eliminated;
the same candidate and output equivalence guards remain explicit. -/
noncomputable def whole_cut_witness_closed : KDerivation
    (imp wholeWitness.encode target.encode) := eliminate_witnesses whole_cut_point

theorem whole_cut_point_certificate : theoremCode (certificate whole_cut_point) =
    imp (equal 33 32) (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
      (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
        (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode))) :=
  certificate_correct whole_cut_point

theorem whole_cut_witness_closed_certificate :
    theoremCode (certificate whole_cut_witness_closed) =
      imp wholeWitness.encode target.encode := certificate_correct whole_cut_witness_closed

end PASoundness.PAtoCompactWholeCutPointClosed

#print axioms PASoundness.PAtoCompactWholeCutPointClosed.whole_cut_point
#print axioms PASoundness.PAtoCompactWholeCutPointClosed.whole_cut_witness_closed
#print axioms PASoundness.PAtoCompactWholeCutPointClosed.whole_cut_point_certificate
#print axioms PASoundness.PAtoCompactWholeCutPointClosed.whole_cut_witness_closed_certificate
