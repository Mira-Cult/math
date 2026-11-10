import PASoundness.PAtoCompactTermTranslation

/-! Exact encoding identity for the direct named successor template used by
the candidate term translator. No renamed-template or quotient law follows. -/
namespace PASoundness.PAtoCompactTermSuccessorIdentity

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactQuotientSuccessor
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp PASoundness.Cantor.pair PASoundness.Cantor.triangle

theorem hd_helper (x : Nat) : (domainTemplate x).encode = (domainFormula x).encode :=
  (domainTemplate_encode x).trans (encode_of_code (candidateCode x 30 31 32 33 34 35 36 37)).symm

theorem hs_helper : (Formula.all 8 (namedSuccessorBody 0 7 8)).encode = rawSuccessorFormula.encode :=
  (show (Formula.all 8 (namedSuccessorBody 0 7 8)).encode = successorCode 0 7 8 from rfl).trans
    (encode_of_code (successorCode 0 7 8)).symm

attribute [local irreducible] domainFormula rawSuccessorFormula domainTemplate

/-- The literal compact encoding matches the previously calibrated template. -/
theorem successorTemplate_encode : successorTemplate.encode = successorFormula.encode := by
  have h0 := hd_helper
  have h1 := hs_helper
  have cg {a a' b b' : Nat} (ha : a = a') (hb : b = b') :
      PASoundness.CompactProof.both a b = PASoundness.CompactProof.both a' b' :=
    (congrArg (fun x => PASoundness.CompactProof.both x b) ha).trans
      (congrArg (PASoundness.CompactProof.both a') hb)
  have hh := cg (h0 0) (cg (h0 1) (cg (h0 7)
    (cg h1 (rfl : (replace 0 7 equivalentFormula).encode = _))))
  have form_encode (a b c d e : Formula) :
      (Formula.ex 7 (andF a (andF b (andF c (andF d e))))).encode =
      PASoundness.CompactProof.existsCode 7
        (PASoundness.CompactProof.both a.encode (PASoundness.CompactProof.both b.encode
          (PASoundness.CompactProof.both c.encode (PASoundness.CompactProof.both d.encode e.encode)))) := by rfl
  have hleft := form_encode (domainTemplate 0) (domainTemplate 1) (domainTemplate 7)
      (Formula.all 8 (namedSuccessorBody 0 7 8)) (replace 0 7 equivalentFormula)
  have hright := form_encode (domainFormula 0) (domainFormula 1) (domainFormula 7)
      rawSuccessorFormula (replace 0 7 equivalentFormula)
  exact hleft.trans ((congrArg (PASoundness.CompactProof.existsCode 7) hh).trans hright.symm)

end PASoundness.PAtoCompactTermSuccessorIdentity

#print axioms PASoundness.PAtoCompactTermSuccessorIdentity.successorTemplate_encode
