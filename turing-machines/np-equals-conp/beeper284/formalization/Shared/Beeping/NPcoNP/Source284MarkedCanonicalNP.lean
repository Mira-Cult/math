import Shared.Beeping.NPcoNP.Source284MarkedGuardedVerifier
import Shared.Beeping.NPcoNP.Source284Bounded

/-! Canonical NP coverage and all-certificate, all-clock soundness for one
finite source verifier with an original-cutoff preserving wrapper. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedCanonicalNP

open Turing ComplexityTheory Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284JoinedHaltingVerifier
open Shared.Beeping.NPcoNP.Source284VerifierUniformBudget (runtimePolynomial)
open Shared.Beeping.NPcoNP.Source284MarkedFramedEncoder (sourceTime sourceDescription)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284Relative

/-- Every canonical NP language has a single finite source verifier whose
polynomially bounded search is complete and whose acceptance is sound for
all certificates and all clocks. No intermediate witness-range premise is
assumed. Physical-table refinement remains separate. -/
theorem canonical_np_source (L : DecisionProblem) (hL : L ∈ ComplexityTheory.NP) :
    ∃ (description k : Nat) (time certificateBits originalCutoff : Polynomial Nat),
      (∀ n, originalCutoff.eval n ≤ Source284DynamicGuardSource.bound k n) ∧
      (∀ (x : List Bool) (inputSuffix : Nat), L x = true →
        acceptBound description (encodeFrame x inputSuffix) (time.eval x.length)
          (2^(certificateBits.eval x.length)) = true) ∧
      (∀ (x : List Bool) (inputSuffix certificate clock : Nat),
        accepts description (encodeFrame x inputSuffix) certificate clock = true → L x = true) := by
  change ∃ (cutoff : Polynomial Nat) (R : List Bool × List Bool → Bool),
    IsPolyTime R ∧ ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ cutoff.eval x.length ∧ R (x,w) at hL
  obtain ⟨cutoff,R,hR,hRlang⟩ := hL
  letI := Source284JoinedHaltingEncoder.machine.kFin
  letI := alphabet
  letI : Inhabited Source284JoinedHaltingEncoder.machine.Λ := ⟨Source284JoinedHaltingEncoder.machine.main⟩
  obtain ⟨width,enc,program,simulation,verifier,k,r,hvalid,hbound,hreject,hguard⟩ :=
    Source284MarkedGuardedVerifier.guarded_source_uniform cutoff cutoff R hR
  let codec := TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc
  let description := sourceDescription codec program k r
  let outerBound := Source284RestoredPolynomialRunway.countPolynomial k+1
  let time := Source284MarkedFramedEncoder.clockPolynomial k r codec outerBound
    (runtimePolynomial width simulation verifier outerBound)
  let bits : Polynomial Nat := 2*cutoff+4
  refine ⟨description,k,time,bits,cutoff,hbound,?_,?_⟩
  · intro x inputSuffix hmem
    obtain ⟨w,hw,haccept⟩ := (hRlang x).1 hmem
    let certificate := Source284TaggedWitnessCodec.encode w
    have hc : certificate < 2^(bits.eval x.length) := by
      have h := Source284TaggedWitnessCodec.encode_lt (cutoff.eval x.length) w hw
      simpa [certificate,bits,Source284WitnessWindow.width,Polynomial.eval_add,
        Polynomial.eval_mul,Nat.add_assoc] using h
    have hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length)
        certificate = some w := Source284TaggedWitnessCodec.decode_encode _ w (le_trans hw (hbound x.length))
    obtain ⟨fuel,_,hverified⟩ := hguard x w (le_trans hw (hbound x.length))
    obtain ⟨hclock,hresult⟩ := hverified certificate inputSuffix hdec
    have ha : accepts description (encodeFrame x inputSuffix) certificate (sourceTime codec k r x w fuel+1) = true := by
      change ((Source284Relative.run description
        (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
        (sourceTime codec k r x w fuel+1)).state == 0) = true
      simpa [description,codec,hw,haccept] using hresult 0
    apply (acceptBound_iff _ _ _ _).2
    refine ⟨certificate,hc,?_⟩
    exact accepts_clock_mono_le description (encodeFrame x inputSuffix) certificate _ _ hclock ha
  · intro x inputSuffix certificate clock haccept
    cases hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate with
    | none =>
      have hbad : Source284TaggedWitnessCodec.decode
          (Source284DynamicGuardSource.bound k (Source284Parser.length (encodeFrame x inputSuffix))) certificate = none := by
        simpa [Source284Parser.length,Source284Parser.parse_encodeFrame] using hdec
      have hfalse := hreject (encodeFrame x inputSuffix) certificate hbad clock
      rw [hfalse] at haccept
      contradiction
    | some w =>
      have hwouter := Source284TaggedWitnessCodec.decode_length (Source284DynamicGuardSource.bound k x.length)
        certificate w hdec
      obtain ⟨fuel,_,hverified⟩ := hguard x w hwouter
      obtain ⟨_,hresult⟩ := hverified certificate inputSuffix hdec
      by_cases hw : w.length ≤ cutoff.eval x.length
      · by_cases hrelation : R (x,w) = true
        · exact (hRlang x).2 ⟨w,hw,hrelation⟩
        · have hfalse : R (x,w) = false := Bool.eq_false_iff.mpr hrelation
          have hafter : ∀ extra, accepts description (encodeFrame x inputSuffix) certificate
              (sourceTime codec k r x w fuel+1+extra) = false := by
            intro extra
            simpa [description,codec,Source284Relative.accepts,hw,hfalse] using hresult extra
          have hnever := Source284PositiveTaggedCutoff.never_of_after description (encodeFrame x inputSuffix)
            certificate (sourceTime codec k r x w fuel+1) hafter clock
          rw [hnever] at haccept
          contradiction
      · have hafter : ∀ extra, accepts description (encodeFrame x inputSuffix) certificate
            (sourceTime codec k r x w fuel+1+extra) = false := by
          intro extra
          simpa [description,codec,Source284Relative.accepts,hw] using hresult extra
        have hnever := Source284PositiveTaggedCutoff.never_of_after description (encodeFrame x inputSuffix)
          certificate (sourceTime codec k r x w fuel+1) hafter clock
        rw [hnever] at haccept
        contradiction

end Shared.Beeping.NPcoNP.Source284MarkedCanonicalNP
