import PASoundness.PAtoCompactCandidateStandard
import PASoundness.PAtoCompactCandidateExact
import PASoundness.PAtoCompactOrdinalEquivalence

/-! A concrete proposed successor relation on the candidate quotient, with
standard-HF calibration. This supplies no K quotient congruence, arithmetic
proof translation, induction, or PA soundness theorem. Named bottom encodes
literal `member 0 0`; its ordinary logical reading here is standard-HF only. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotientSuccessor
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactCandidateStandard PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactOrdinalEquivalence PASoundness.PAtoCompactZeroSuccessor
open PASoundness.CompactMatrix (Environment update decode)
open PASoundness.HFCoding

private def andF (a b : Formula) : Formula := (a.imp b.not).not

/-- The named form of the exact transitivity/extrema candidate code. The
internal candidate binders are 30 through 37, distinct from 0, 1, and 7. -/
def domainFormula (x : Nat) : Formula :=
  ofDecoded (decode (candidateCode x 30 31 32 33 34 35 36 37))

/-- Raw successor of name 0 into the witness named 7, with test binder 8. -/
def rawSuccessorFormula : Formula :=
  ofDecoded (decode (successorCode 0 7 8))

/-- The quotient-successor proposal: for inputs named 0 and 1, there is a
candidate witness 7 that is a raw successor of 0 and is equivalent to 1;
the inputs themselves also satisfy the exact candidate-domain predicate. -/
def successorFormula : Formula := .ex 7
  (andF (domainFormula 0) (andF (domainFormula 1) (andF (domainFormula 7)
    (andF rawSuccessorFormula (replace 0 7 equivalentFormula)))))

private theorem andF_meaning (a b : Formula) (ρ : Environment) :
    (andF a b).Realize ρ ↔ a.Realize ρ ∧ b.Realize ρ := by
  simp [andF, Formula.not, Formula.Realize]

private theorem domain_meaning (x : Nat) (ρ : Environment)
    (fresh : [x,30,31,32,33,34,35,36,37].Nodup) :
    (domainFormula x).Realize ρ ↔ ∃ n, ρ x = (ordinal n).code := by
  rw [← Formula.encode_realize]
  simpa only [domainFormula, encode_of_code, candidateCode] using
    candidate_standard_iff x 30 31 32 33 34 35 36 37 ρ fresh

private theorem raw_meaning (ρ : Environment) (n : Nat)
    (h : ρ 0 = (ordinal n).code) :
    rawSuccessorFormula.Realize ρ ↔ ρ 7 = (ordinal (n+1)).code := by
  rw [← Formula.encode_realize]
  simpa only [rawSuccessorFormula, encode_of_code] using
    ordinal_successor_relation 0 7 8 n ρ (by decide) (by decide) h

private theorem eq_meaning (ρ : Environment) (n m : Nat)
    (h7 : ρ 7 = (ordinal n).code) (h1 : ρ 1 = (ordinal m).code) :
    (replace 0 7 equivalentFormula).Realize ρ ↔ n = m := by
  have h0 : 0 ∉ equivalentFormula.binders := by decide
  have h7' : 7 ∉ equivalentFormula.binders := by decide
  rw [replace_realize 0 7 equivalentFormula h0 h7']
  have h := standard_ordinal_iff (update ρ 0 (ρ 7)) n m
    (by simp [update, h7]) (by simpa [update] using h1)
  rw [Formula.encode_realize] at h
  exact h

/-- The exact literal compact encoding of this successor proposal is true
on standard finite ordinal codes exactly for the arithmetic successor pair. -/
theorem standard_ordinal_successor_iff (ρ : Environment) (n m : Nat)
    (h0 : ρ 0 = (ordinal n).code) (h1 : ρ 1 = (ordinal m).code) :
    (decode successorFormula.encode).Realize ρ ↔ m = n + 1 := by
  rw [Formula.encode_realize]
  change (∃ z, (andF (domainFormula 0) (andF (domainFormula 1)
    (andF (domainFormula 7) (andF rawSuccessorFormula
      (replace 0 7 equivalentFormula))))).Realize (update ρ 7 z)) ↔ _
  simp only [andF_meaning]
  constructor
  · rintro ⟨z,_,_,_,hs,he⟩
    have hx : (update ρ 7 z) 0 = (ordinal n).code := by simpa [update] using h0
    have hz : z = (ordinal (n+1)).code := by
      have hh := (raw_meaning (update ρ 7 z) n hx).mp hs
      simpa [update] using hh
    have h7 : (update ρ 7 z) 7 = (ordinal (n+1)).code := by simp [update, hz]
    have hy : (update ρ 7 z) 1 = (ordinal m).code := by simpa [update] using h1
    have hnm := (eq_meaning (update ρ 7 z) (n+1) m h7 hy).mp he
    exact hnm.symm
  · intro hmn
    let z := (ordinal (n+1)).code
    let η := update ρ 7 z
    have hx : η 0 = (ordinal n).code := by simpa [η, update] using h0
    have hy : η 1 = (ordinal m).code := by simpa [η, update] using h1
    have hz : η 7 = (ordinal (n+1)).code := by simp [η, z]
    refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
    · exact (domain_meaning 0 η (by decide)).mpr ⟨n,hx⟩
    · exact (domain_meaning 1 η (by decide)).mpr ⟨m,hy⟩
    · exact (domain_meaning 7 η (by decide)).mpr ⟨n+1,hz⟩
    · exact (raw_meaning η n hx).mpr hz
    · exact (eq_meaning η (n+1) m hz hy).mpr hmn.symm

end PASoundness.PAtoCompactQuotientSuccessor

#print axioms PASoundness.PAtoCompactQuotientSuccessor.standard_ordinal_successor_iff
