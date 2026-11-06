import Shared.Beeping.NPcoNP.Source284MarkedLoadedReject
import Shared.Beeping.NPcoNP.Source284VerifierUniformBudget
import Shared.Beeping.NPcoNP.Source284JoinedHaltingVerifier

/-! A canonical polynomial-time relation with an actual dynamic guard and
independently grown two-sided serializer workspace. The wrapper preserves its
original witness cutoff even for every larger witness accepted by the guard. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedGuardedVerifier

open Turing ComplexityTheory Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Shared.Beeping.NPcoNP.Source284JoinedHaltingVerifier
open Shared.Beeping.NPcoNP.Source284VerifierPredecessor (result_predecessor result_step_of_window)
open Shared.Beeping.NPcoNP.Source284VerifierUniformBudget (runtimePolynomial runwayPolynomial demands_bounded)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable (word)
open Shared.Beeping.NPcoNP.Source284FramedEncoder (serialClock)
open Shared.Beeping.NPcoNP.Source284MarkedFramedEncoder (sourceTime sourceDescription)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

/-- One finite source table computes the original-cutoff guarded relation
for every witness under the generated outer bound, including the interval
above the original cutoff. Invalid outer decodings cannot accept at any clock. -/
theorem guarded_source_uniform (cutoff witnessBound : Polynomial Nat)
    (R : List Bool × List Bool → Bool) (hR : IsPolyTime R) :
    letI := Source284JoinedHaltingEncoder.machine.kFin
    letI := alphabet
    letI : Inhabited Source284JoinedHaltingEncoder.machine.Λ := ⟨Source284JoinedHaltingEncoder.machine.main⟩
    ∃ (width : Nat) (enc : Alphabet Source284JoinedHaltingEncoder.machine → List.Vector Bool width)
      (program : Program) (simulation verifier : Polynomial Nat) (k r : Nat),
      let outerBound := Source284RestoredPolynomialRunway.countPolynomial k+1
      valid program = true ∧
      (∀ n, witnessBound.eval n ≤ Source284DynamicGuardSource.bound k n) ∧
      (∀ (input certificate : Nat),
        Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k (Source284Parser.length input))
          certificate = none →
        ∀ clock, Source284Relative.accepts
          (sourceDescription (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) program k r)
          input certificate clock = false) ∧
      ∀ x w : List Bool, w.length ≤ Source284DynamicGuardSource.bound k x.length →
        ∃ fuel ≤ (runtimePolynomial width simulation verifier outerBound).eval x.length,
          ∀ (certificate inputSuffix : Nat),
            Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w →
            sourceTime (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) k r x w fuel+1 ≤
              (Source284MarkedFramedEncoder.clockPolynomial k r
                (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) outerBound
                (runtimePolynomial width simulation verifier outerBound)).eval x.length ∧
            ∀ extra, ((Source284Relative.run
              (sourceDescription (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) program k r)
              (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
              (sourceTime (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) k r x w fuel+1+extra)).state == 0) =
                (if w.length ≤ cutoff.eval x.length then R (x,w) else false) := by
  letI := Source284JoinedHaltingEncoder.machine.kFin
  letI := alphabet
  letI : Inhabited Source284JoinedHaltingEncoder.machine.Λ := ⟨Source284JoinedHaltingEncoder.machine.main⟩
  obtain ⟨width,enc,program,simulation,verifier,hvalid,hcombined⟩ := encoded_joined_verifier cutoff R hR
  obtain ⟨k,hk⟩ := Source284DynamicGuardSource.bound_dominates witnessBound
  let outerBound := Source284RestoredPolynomialRunway.countPolynomial k+1
  let demand := runwayPolynomial width simulation verifier outerBound
  obtain ⟨r,hr⟩ := Source284MarkedFramedEncoder.uniform_workspace_for_k k demand demand
  refine ⟨width,enc,program,simulation,verifier,k,r,hvalid,hk,?_,?_⟩
  · intro input certificate hbad
    exact Source284MarkedFramedEncoder.rejected_raw_never_accepts
      (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)
      program hvalid k r input certificate hbad
  · intro x w hw
    have hbound : w.length ≤ outerBound.eval x.length := by
      have hb : Source284DynamicGuardSource.bound k x.length ≤ Source284PolynomialMarkedCleanup.count k x.length+1 :=
        Nat.div_le_self _ _
      simp only [outerBound,Polynomial.eval_add,Polynomial.eval_one,
        Source284RestoredPolynomialRunway.countPolynomial_eval]
      omega
    obtain ⟨first,bs,d,hrev,hd,hrun⟩ := hcombined x w
    obtain ⟨fuel,hfuel,⟨q,reference⟩,hpre,hstep⟩ := result_predecessor program _ _ _ hrun
    have hpre' : run program (initial (inputBits Source284JoinedRawEncodeTM2.machine
        (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) (joinedBits x w))) fuel =
          some (.inr (q,reference)) := by
      simpa only [← protected_input_agrees enc (joinedBits x w)] using hpre
    have hq := Shared.Codes.FiniteProgramLink.run_in_range program hvalid
      (initial (inputBits Source284JoinedRawEncodeTM2.machine
        (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) (joinedBits x w)))
      (by simpa [initial] using Shared.Codes.FiniteProgramLink.valid_nonempty program hvalid) fuel
    rw [hpre'] at hq
    obtain ⟨htime,hinput,hwitness⟩ := demands_bounded enc simulation verifier outerBound x w
      first bs d fuel hbound hrev hd hfuel
    have hinput' : 1+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine
        (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) (joinedBits x w)).length+3) ≤
        Source284CheckpointWorkspace.workspace k r x.length := le_trans hinput (hr x.length).1
    have hwitness' : (word (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)).length+
        (1+serialClock (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) x w fuel) ≤
        Source284CheckpointMarkedWorkspace.markCount k r x.length-1 := le_trans hwitness (hr x.length).2
    refine ⟨fuel,htime,?_⟩
    intro certificate inputSuffix hdec
    refine ⟨Source284MarkedFramedEncoder.sourceTime_polynomial
      (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) k r outerBound
        (runtimePolynomial width simulation verifier outerBound) x w certificate fuel hdec hbound htime,?_⟩
    intro extra
    obtain ⟨_,actualTape,rev,revSource,_,hwindow,hsource⟩ :=
      Source284MarkedFramedEncoder.source_encoder_window
        (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)
        program hvalid k r x w certificate inputSuffix 1 1 fuel q reference hdec hpre' hinput' hwitness'
    have ha := result_step_of_window program q actualTape reference rev _ hwindow hstep
    have hout := Source284MarkedLoadedTerminal.loaded_terminal_step
      (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)
      program k r x w certificate inputSuffix fuel q actualTape revSource _ hvalid hq hdec ha hsource
    cases hb : (if w.length ≤ cutoff.eval x.length then R (x,w) else false) with
    | false =>
      have ha' : step program (q,actualTape) = some (.inl false) := by simpa [hb] using ha
      have hs := Source284MarkedLoadedReject.loaded_false_stable
        (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)
        program k r x w certificate inputSuffix fuel q actualTape revSource hvalid hq hdec ha' hsource extra
      simpa [hb] using hs
    | true =>
      have hy : ((Source284Relative.run
          (sourceDescription (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) program k r)
          (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
          (sourceTime (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) k r x w fuel+1)).state == 0) = true := by
        simpa [hb] using hout
      have hz : (Source284Relative.run
          (sourceDescription (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) program k r)
          (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
          (sourceTime (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) k r x w fuel+1)).state = 0 := by
        simpa using hy
      rw [Source284Relative.run_add_clock,Source284Relative.run_absorbing _ _ hz]
      simpa [hb] using hy

end Shared.Beeping.NPcoNP.Source284MarkedGuardedVerifier
