import PASoundness.PAtoCompactCandidateMemberClosure
import PASoundness.PAtoCompactCandidateFieldTransport
import PASoundness.PAtoCompactPartialCompositionAtSource
import PASoundness.PAtoCompactScopedActiveReplace

/-! A supplied candidate whole and an equal-or-member cut provide the
literal candidate code for that cut. The member case explicitly freshens
the two binders introduced by candidate-member closure. -/
namespace PASoundness.PAtoCompactSeededSpanCutCandidate

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateMemberClosure PASoundness.PAtoCompactCandidateFieldTransport
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceRelation : Formula := namedEither (.equal 40 0) (.member 0 40)
def targetRelation : Formula := namedEither (.equal 41 8) (.member 8 41)

private theorem candidate_code (x : Nat) : (namedCandidate x).encode =
    candidateCode x 37 32 33 34 30 35 13 36 := by rfl

/-- The source cut is a candidate under the explicit candidate whole and
equal-or-member relation. -/
def source_cut_candidate : KDerivation (imp (namedCandidate 0).encode
    (imp sourceRelation.encode (namedCandidate 40).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [sourceRelation.encode, (namedCandidate 0).encode]
  have hr : Context Γ sourceRelation.encode := .head _ _
  have hw : Context Γ (namedCandidate 0).encode := .hypothesis (by simp [Γ])
  apply Context.disjunctionElim hr
  · let Δ := equal 40 0 :: Γ
    have he : Context Δ (equal 40 0) := .head _ _
    have hw' : Context Δ (namedCandidate 0).encode := .under hw _
    have hreplace := (equalityReplace 0 40 (namedCandidate 0) (by decide) (by decide)).1
    have hc : Context Δ (replace 0 40 (namedCandidate 0)).encode :=
      .mp hw' (.mp (Context.eqSymm he) (.closed hreplace))
    have hshape : replace 0 40 (namedCandidate 0) = namedCandidate 40 := by decide
    rw [hshape] at hc
    exact hc
  · let Δ := member 0 40 :: Γ
    have hm : Context Δ (member 0 40) := .head _ _
    have hw' : Context Δ (candidateCode 0 37 32 33 34 30 35 13 36) := by
      simpa only [candidate_code] using Context.under hw (member 0 40)
    have hc : Context Δ (candidateCode 40 42 32 33 43 30 35 13 36) :=
      .mp hm (.mp hw' (.closed (candidate_member 0 40 37 32 33 42 34 30 35 13 36 43 44 (by decide))))
    have hm' : Context Δ (candidateCode 40 37 32 33 43 30 35 13 36) :=
      .mp hc (.closed (member_field 40 42 32 33 43 30 35 13 36 37 (by decide)))
    have hs : Context Δ (candidateCode 40 37 32 33 34 30 35 13 36) :=
      .mp hm' (.closed (subset_field 40 37 32 33 43 30 35 13 36 34 (by decide) (by decide)))
    simpa only [candidate_code, Δ, Γ, Formula.encode] using hs

private def sourceFrame : Formula := .imp (namedCandidate 0) (.imp sourceRelation (namedCandidate 40))
private def moved8 : Formula := replace 0 8 sourceFrame

/-- The target cut satisfies the analogous explicit candidate code. -/
def target_cut_candidate : KDerivation (imp (namedCandidate 8).encode
    (imp targetRelation.encode (namedCandidate 41).encode)) := by
  have hbase : KDerivation sourceFrame.encode := by
    simpa only [sourceFrame, Formula.encode] using source_cut_candidate
  have h8 := replace_derivation 0 8 sourceFrame (by decide) (by decide) hbase
  have h41 := replace_derivation 40 41 moved8 (by decide) (by decide) (by simpa only [moved8] using h8)
  have halign : replace 40 41 moved8 = .imp (namedCandidate 8) (.imp targetRelation (namedCandidate 41)) := by decide
  rw [halign] at h41
  exact h41

theorem source_cut_candidate_certificate : theoremCode (certificate source_cut_candidate) =
    imp (namedCandidate 0).encode (imp sourceRelation.encode (namedCandidate 40).encode) :=
  certificate_correct source_cut_candidate
theorem target_cut_candidate_certificate : theoremCode (certificate target_cut_candidate) =
    imp (namedCandidate 8).encode (imp targetRelation.encode (namedCandidate 41).encode) :=
  certificate_correct target_cut_candidate

end PASoundness.PAtoCompactSeededSpanCutCandidate

#print axioms PASoundness.PAtoCompactSeededSpanCutCandidate.sourceRelation
#print axioms PASoundness.PAtoCompactSeededSpanCutCandidate.targetRelation
#print axioms PASoundness.PAtoCompactSeededSpanCutCandidate.source_cut_candidate
#print axioms PASoundness.PAtoCompactSeededSpanCutCandidate.target_cut_candidate
#print axioms PASoundness.PAtoCompactSeededSpanCutCandidate.source_cut_candidate_certificate
#print axioms PASoundness.PAtoCompactSeededSpanCutCandidate.target_cut_candidate_certificate
