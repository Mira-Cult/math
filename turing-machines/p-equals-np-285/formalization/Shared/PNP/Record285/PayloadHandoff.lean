import Shared.PNP.Record285.PayloadEncoding

/-! Attach a continuation to the encoded reversed-payload tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PayloadHandoff
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftStatus run_shift)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Codes.FiniteProgramTwoExit
open Shared.Codes.FiniteProgramUntag (cursor padding)

abbrev source := PayloadEncoding.program

theorem source_length : source.length = 225 := by decide

theorem source_stop (tape : Tape) : step source (194,tape) = some (.inl false) := by
  have hr : source[194]? = some ((false,true,182,1),(true,true,182,1)) := by decide
  cases h : tape.2.1 <;> simp [step,hr,h]

def program (p : Program) : Program := Shared.Codes.FiniteProgramTwoExit.program source p 194 194

theorem program_valid (p : Program) (hp : valid p = true) : valid (program p) = true :=
  Shared.Codes.FiniteProgramTwoExit.program_valid source p 194 194 PayloadEncoding.program_valid hp
    (by rw [source_length]; decide) (by rw [source_length]; decide)

theorem blank_start_handoff (p : Program) (payload : List Bool) :
    ∃ tape, run (program p) (initial (CanonicalInput.canonical payload))
      (PayloadEncoding.duration payload+2) = some (.inr (227,tape)) ∧
      TapeRel tape (Shared.Codes.FiniteProgramSingleUntag.rawTape (PayloadEncoding.words payload)) := by
  obtain ⟨tape,hr,ht⟩ := PayloadEncoding.blank_start_payload payload
  have hr' := first_entry source p 194 194 (initial (CanonicalInput.canonical payload))
    (194,tape) (PayloadEncoding.duration payload)
    PayloadEncoding.program_valid (by rw [source_length]; simp [initial]) source_stop source_stop hr
  change run (program p) (initial (CanonicalInput.canonical payload)) _ = _ at hr'
  let cur := cursor false [] (PayloadEncoding.words payload)
  let L := cur.2
  let R := false::padding (PayloadEncoding.words payload).length [false,false]
  let t := tapeAt L (cur.1::false::R)
  have hshape : Shared.Codes.FiniteProgramSingleUntag.rawTape (PayloadEncoding.words payload) = t := by rfl
  have hrel : TapeRel tape t := ht.trans (by rw [hshape])
  have hh := handoff_second source p 194 194 (by rw [source_length]; decide) cur.1 false L R
  change run (program p) (194,t) 2 = some (.inr (227,t)) at hh
  have hrun := run_related (program p) (194,tape) (194,t) rfl hrel 2
  rw [hh] at hrun
  cases hactual : run (program p) (194,tape) 2 with
  | none => rw [hactual] at hrun; exact False.elim hrun
  | some v => cases v with
    | inl b => rw [hactual] at hrun; exact False.elim hrun
    | inr d =>
      rw [hactual] at hrun
      have hd : d.1 = 227 ∧ TapeRel d.2 t := hrun
      refine ⟨d.2,?_,hd.2.trans (by rw [hshape])⟩
      rw [run_continue _ _ _ _ _ hr',hactual]
      cases d with | mk q t => simp only at hd; rw [hd.1]

theorem blank_start_then_continue (p : Program) (hp : valid p = true)
    (payload : List Bool) (fuel : Nat) :
    StatusRel (run (program p) (initial (CanonicalInput.canonical payload))
        (PayloadEncoding.duration payload+2+fuel))
      (shiftStatus 227 (run p (0,Shared.Codes.FiniteProgramSingleUntag.rawTape (PayloadEncoding.words payload)) fuel)) := by
  obtain ⟨tape,hload,htape⟩ := blank_start_handoff p payload
  rw [run_continue _ _ _ _ _ hload]
  have hq : (0 : Nat) < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  have hs := run_shift (pre source 194 194) p [] hp (0,tape) hq fuel
  have hlen : (pre source 194 194).length = 227 := by rw [pre_length,source_length]
  rw [hlen] at hs
  change run (program p) (227,tape) fuel = shiftStatus 227 (run p (0,tape) fuel) at hs
  rw [hs]
  exact FrameBufferHandoff.shift_status_related 227 _ _
    (run_related p (0,tape) (0,Shared.Codes.FiniteProgramSingleUntag.rawTape (PayloadEncoding.words payload)) rfl htape fuel)

def reflectedProgram (p : Program) : Program :=
  program (Shared.Codes.FiniteProgramMirror.program p)

theorem reflectedProgram_valid (p : Program) (hp : valid p = true) : valid (reflectedProgram p) = true := by
  apply program_valid
  simpa [Shared.Codes.FiniteProgramMirror.valid_mirror] using hp

/-- A mirrored continuation sees the canonical encoded reversed payload,
with exact timeout behavior after the paid blank-start preparation. -/
theorem bounded_reflected (p : Program) (hp : valid p = true) (payload : List Bool) (fuel : Nat) :
    bounded (reflectedProgram p) (CanonicalInput.canonical payload)
      (PayloadEncoding.duration payload+2+fuel) =
      bounded p (BitstringEncoding.bitEncode payload.reverse) fuel := by
  let mirror := Shared.Codes.FiniteProgramMirror.program p
  let target := BitstringEncoding.bitEncode payload.reverse
  have hm : valid mirror = true := by
    simpa [mirror,Shared.Codes.FiniteProgramMirror.valid_mirror] using hp
  have hs := blank_start_then_continue mirror hm payload fuel
  have hr := Shared.Codes.FiniteProgramTapeEquiv.result_related _ _ hs
  rw [Shared.Codes.FiniteProgramLink.result_shift] at hr
  have ht := Shared.Codes.FiniteProgramTapeEquiv.run_result_congr mirror
    (0,Shared.Codes.FiniteProgramSingleUntag.rawTape (PayloadEncoding.words payload)) (Shared.Codes.FiniteProgramMirror.config (initial target))
    (by rfl) (PayloadEncoding.raw_reflected payload) fuel
  change Shared.Codes.FiniteProgramTapeEquiv.result
    (run mirror (0,Shared.Codes.FiniteProgramSingleUntag.rawTape (PayloadEncoding.words payload)) fuel) = _ at ht
  dsimp only [mirror] at ht
  rw [Shared.Codes.FiniteProgramMirror.run_mirror] at ht
  have hmirror (s : Status) :
      Shared.Codes.FiniteProgramTapeEquiv.result (Shared.Codes.FiniteProgramMirror.status s) =
        Shared.Codes.FiniteProgramTapeEquiv.result s := by
    cases s with
    | none => rfl
    | some v => cases v <;> rfl
  rw [hmirror] at ht
  unfold bounded
  change Shared.Codes.FiniteProgramTapeEquiv.result
      (run (program mirror) (initial (CanonicalInput.canonical payload))
        (PayloadEncoding.duration payload+2+fuel)) =
    Shared.Codes.FiniteProgramTapeEquiv.result (run p (initial target) fuel)
  exact hr.trans ht

theorem handoff_bound (payload : List Bool) :
    PayloadEncoding.duration payload+2 ≤ payload.length*(288*payload.length+200)+30 := by
  have h := PayloadEncoding.duration_bound payload
  omega

end Shared.PNP.Record285.PayloadHandoff
