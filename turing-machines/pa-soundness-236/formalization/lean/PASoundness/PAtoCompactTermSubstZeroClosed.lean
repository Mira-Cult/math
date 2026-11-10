import PASoundness.PAtoCompactTermSubstZeroInduction
import PASoundness.PAtoCompactRetainedZeroLeafClosed

/-! Finite-K selected zero substitution for arbitrary source terms. The
zero-output transport and every variable leaf are constructed; explicit
allocation bounds remain. No semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactTermSubstZeroClosed
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstPolymorphic
open PASoundness.PAtoCompactTermSubstZeroInduction PASoundness.PAtoCompactRetainedZeroLeafClosed

/-- Both K graph alignments after substituting selected source variables by
zero or by its value name q. Arbitrary decidable source-variable types preserve
free/bound provenance; mapped target names may alias. -/
noncomputable def selected_zero_substitution_closed
    {α : Type} [DecidableEq α] (selected : α → Prop) [DecidablePred selected]
    (name : α → Nat) (g : Formula) (q d : Nat) (hqd : q < d)
    (s : Peano.language.Term α) (b out : Nat) (hout : out < b)
    (hH : ∀ a ∈ (retainedZero g q d).free, a < b)
    (hs : ∀ a ∈ (s.subst (fun a => if selected a then .var q else .var (name a))).varFinset, a < b)
    (ht : ∀ a ∈ (s.subst (fun a => if selected a then Peano.zero else .var (name a))).varFinset, a < b) :
    Align (retainedZero g q d)
      (s.subst (fun a => if selected a then .var q else .var (name a)))
      (s.subst (fun a => if selected a then Peano.zero else .var (name a))) b out :=
  selected_zero_substitution selected name g q d
    (fun base result hr hq _ => retained_zero_leaf_closed g q d base result hqd hq hr)
    s b out hout hH hs ht

end PASoundness.PAtoCompactTermSubstZeroClosed

#print axioms PASoundness.PAtoCompactTermSubstZeroClosed.selected_zero_substitution_closed
