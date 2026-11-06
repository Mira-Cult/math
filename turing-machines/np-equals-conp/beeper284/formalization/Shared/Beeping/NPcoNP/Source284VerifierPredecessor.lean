import Shared.Beeping.NPcoNP.Source284JoinedHaltingVerifier
import Shared.Beeping.NPcoNP.Source284FramedEncoderCoverage

/-! A completed finite verifier run has a last live configuration. The raw
source loader reaches a window matching that configuration, with a matching
terminal row. This does not yet execute that row in the enclosing source table. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284VerifierPredecessor

open Turing ComplexityTheory Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Shared.Beeping.NPcoNP.Source284JoinedHaltingVerifier
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented digit)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable (word)
open Shared.Beeping.NPcoNP.Source284FramedEncoder (serialClock sourceTime sourceDescription target)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

/-- The first terminal transition occurs strictly before any clock at which
the Boolean result is observed; all earlier execution is explicitly live. -/
theorem result_predecessor (p : Program) (c : Config) (n : Nat) (b : Bool)
    (h : run p c n = some (.inl b)) :
    ∃ t < n, ∃ last, run p c t = some (.inr last) ∧ step p last = some (.inl b) := by
  induction n with
  | zero => simp [run] at h
  | succ n ih =>
    rw [run_succ] at h
    cases hr : run p c n with
    | none => simp [hr,advance] at h
    | some s =>
      cases s with
      | inl b' =>
        simp only [hr,advance,Option.some.injEq,Sum.inl.injEq] at h
        subst b'
        obtain ⟨t,ht,last,hl,hs⟩ := ih hr
        exact ⟨t,by omega,last,hl,hs⟩
      | inr last =>
        refine ⟨n,by omega,last,hr,?_⟩
        simpa [hr,advance] using h

/-- One-cell source-window agreement gives the same scanned finite-tape
bit, so the two configurations take exactly the same result row. -/
theorem result_step_of_window (p : Program) (q : Nat) (a r : Tape) (rev b : Bool)
    (hw : Window 1 (represented a rev (codeState q rev)) (represented r rev (codeState q rev)))
    (hr : step p (q,r) = some (.inl b)) : step p (q,a) = some (.inl b) := by
  have hh := Source284BitWindow.agree_head hw.2.2
  rw [Source284FiniteTapeStep.represented_read,Source284FiniteTapeStep.represented_read] at hh
  have hbit : a.2.1 = r.2.1 := by
    cases ha : a.2.1 <;> cases hb : r.2.1 <;> simp [digit,ha,hb] at hh ⊢
  cases hrows : p[q]? with
  | none => simp [step,hrows] at hr
  | some rows =>
    cases htag : (if r.2.1 then rows.2 else rows.1).2.2.2 with
    | zero => simp [step,hrows,htag] at hr
    | succ k =>
      cases k with
      | zero => simpa [step,hrows,hbit,htag] using hr
      | succ k =>
        cases k with
        | zero => simpa [step,hrows,hbit,htag] using hr
        | succ k => simp [step,hrows,htag] at hr

/-- The standalone compiled source takes its own physical terminal step and
exposes the same Boolean outcome in its acceptance state. -/
theorem compiled_result_step (p : Program) (q : Nat) (t : Tape) (rev b : Bool)
    (hv : valid p = true) (hq : q < p.length) (hr : step p (q,t) = some (.inl b)) :
    ((Source284Relative.step (Source284CompileRecords.compile p)
      (represented t rev (codeState q rev))).state == 0) = b := by
  have hh := Source284FiniteProgramRun.run_acceptance p
    (Source284FiniteProgramRun.closed_of_valid p hv) q t rev hq 1
  have hrun : run p (q,t) 1 = some (.inl b) := by simpa [run,advance] using hr
  rw [hrun] at hh
  change ((Source284Relative.step (Source284CompileRecords.compile p)
    (represented t rev (codeState q rev))).state = 0) ↔ _ at hh
  cases b <;> simp_all

/-- One fixed source continuation reaches, for each exact joined input and
valid tagged witness, the last live verifier configuration. The stated two
runway inequalities are still required; the final enclosing-source transition
and the literal physical table are not claimed here. -/
theorem guarded_source_predecessor (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (hR : IsPolyTime R) :
    letI := Source284JoinedHaltingEncoder.machine.kFin
    letI := alphabet
    letI : Inhabited Source284JoinedHaltingEncoder.machine.Λ := ⟨Source284JoinedHaltingEncoder.machine.main⟩
    ∃ (width : Nat) (enc : Alphabet Source284JoinedHaltingEncoder.machine → List.Vector Bool width)
      (program : Program) (bound verifierClock : Polynomial Nat),
      valid program = true ∧ ∀ x w : List Bool,
        let bits := BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))
        ∃ (first : Bool) (bs : List Bool) (d fuel q : Nat) (reference : Tape),
          bits.reverse = first::bs ∧ d ≤ bound.eval (joinedBits x w).length ∧
          fuel < d+2+(TM2OutputProtectedRaw.cost Source284JoinedHaltingEncoder.machine enc
            (Equiv.refl Bool) bits bs+2+verifierClock.eval bits.length) ∧
          run program (initial (inputBits Source284JoinedRawEncodeTM2.machine
            (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) (joinedBits x w))) fuel =
              some (.inr (q,reference)) ∧
          q < program.length ∧
          step program (q,reference) =
            some (.inl (if w.length ≤ p.eval x.length then R (x,w) else false)) ∧
          ∀ (k limit certificate inputSuffix : Nat),
            Source284TaggedWitnessCodec.decode limit certificate = some w →
            1+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine
              (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) (joinedBits x w)).length+3)
                ≤ k*(x.length*x.length)+2 →
            (word (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)).length+
              (1+serialClock (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) x w fuel)
                ≤ firstZeros k x.length+2*x.length+4 →
            ∃ witnessSuffix actualTape revSource,
              certificate = 4*encodeFrame w witnessSuffix ∧
              step program (q,actualTape) =
                some (.inl (if w.length ≤ p.eval x.length then R (x,w) else false)) ∧
              ((Source284Relative.step (Source284CompileRecords.compile program)
                (represented actualTape revSource (codeState q revSource))).state == 0) =
                  (if w.length ≤ p.eval x.length then R (x,w) else false) ∧
              Window 1
                (Source284Relative.run
                  (sourceDescription (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) program k)
                  (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
                  (sourceTime (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) k x w fuel))
                (Source284SourceRelocation.lift (1292+220*k)
                  (target (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)
                    program (q,actualTape) revSource)) := by
  letI := Source284JoinedHaltingEncoder.machine.kFin
  letI := alphabet
  letI : Inhabited Source284JoinedHaltingEncoder.machine.Λ := ⟨Source284JoinedHaltingEncoder.machine.main⟩
  obtain ⟨width,enc,program,bound,vc,hvalid,hcombined⟩ := encoded_joined_verifier p R hR
  refine ⟨width,enc,program,bound,vc,hvalid,?_⟩
  intro x w
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
  refine ⟨first,bs,d,fuel,q,reference,hrev,hd,hfuel,hpre',hq,hstep,?_⟩
  intro k limit certificate inputSuffix hdec hi hw
  obtain ⟨ws,actual,rev,revSource,hcert,hwindow,hsource⟩ :=
    Source284FramedEncoderCoverage.decoded_encoder_window
      (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)
      program hvalid k limit certificate x w inputSuffix 1 1 fuel q reference hdec hpre' hi hw
  have ha := result_step_of_window program q actual reference rev _ hwindow hstep
  exact ⟨ws,actual,revSource,hcert,ha,
    compiled_result_step program q actual revSource _ hvalid hq ha,hsource⟩

end Shared.Beeping.NPcoNP.Source284VerifierPredecessor
