import Shared.PNP.Record285.FrameBufferSeek

/-! A reversible finite-table probe of the extracted `(data, true-tag)`
buffer. It does not yet serialize the canonical frame. -/
namespace Shared.PNP.Record285.FramePairProbe
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftStatus shiftConfig run_shift)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.PNP.Record285.CanonicalInput

def rows : Program :=
  [((false,false,1,0),(true,false,1,0)),
   ((false,false,2,0),(true,false,3,0)),
   ((false,true,4,0),(true,true,6,0)),
   ((false,true,5,0),(true,true,7,0)),
   ((false,true,10,0),(true,true,10,0)),
   ((false,true,10,0),(true,true,10,0)),
   ((false,true,8,0),(true,true,8,0)),
   ((false,true,9,0),(true,true,9,0))]

def dummy : Program := [((false,true,0,1),(true,true,0,1)),
  ((false,true,0,1),(true,true,0,1)),((false,true,0,1),(true,true,0,1))]
def program (p : Program) : Program := link rows p []

theorem program_valid (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length) :
    valid (program p) = true := by
  have hd : valid (link rows dummy []) = true := by decide
  exact Shared.Codes.FiniteProgramRelink.valid_relink rows dummy p hd hp hlen

def bitState (b : Bool) : Nat := if b then 9 else 8

/-- Four transitions inspect a real tagged bit and return the head and the
entire tape to their starting position; the exit state carries the data bit. -/
theorem probe_bit (p : Program) (head bit : Bool) (left right : List Bool) :
    run (program p) (0,tapeAt (bit::true::left) (head::right)) 4 =
      some (.inr (bitState bit,tapeAt (bit::true::left) (head::right))) := by
  cases head <;> cases bit <;>
    simp [run,advance,step,program,link,rows,bitState,tapeAt,moveTape]

/-- Two blank cells signal the end even if arbitrary data lies beyond them.
The head and tape return exactly to the starting position. -/
theorem probe_end (p : Program) (head : Bool) (left right : List Bool) :
    run (program p) (0,tapeAt (false::false::left) (head::right)) 4 =
      some (.inr (10,tapeAt (false::false::left) (head::right))) := by
  cases head <;> simp [run,advance,step,program,link,rows,tapeAt,moveTape]

theorem probe_bit_then_continue (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length)
    (head bit : Bool) (left right : List Bool) (fuel : Nat) :
    run (program p) (0,tapeAt (bit::true::left) (head::right)) (4+fuel) =
      shiftStatus 8 (run p ((if bit then 1 else 0),tapeAt (bit::true::left) (head::right)) fuel) := by
  rw [run_continue _ _ _ _ _ (probe_bit p head bit left right)]
  cases bit with
  | false =>
    have h := run_shift rows p [] hp (0,tapeAt (false::true::left) (head::right)) (by omega) fuel
    simpa [program,rows,bitState,shiftConfig] using h
  | true =>
    have h := run_shift rows p [] hp (1,tapeAt (true::true::left) (head::right)) (by omega) fuel
    simpa [program,rows,bitState,shiftConfig] using h

theorem probe_end_then_continue (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length)
    (head : Bool) (left right : List Bool) (fuel : Nat) :
    run (program p) (0,tapeAt (false::false::left) (head::right)) (4+fuel) =
      shiftStatus 8 (run p (2,tapeAt (false::false::left) (head::right)) fuel) := by
  rw [run_continue _ _ _ _ _ (probe_end p head left right)]
  have h := run_shift rows p [] hp (2,tapeAt (false::false::left) (head::right)) (by omega) fuel
  simpa [program,rows,shiftConfig] using h

/-- For a nonempty blank-start frame, the first payload bit selects the
corresponding continuation state; the tagged tape itself is unchanged. -/
theorem blank_start_nonempty (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length)
    (bit : Bool) (rest : List Bool) (fuel : Nat) :
    let payload := bit::rest
    let out := tapeAt (FrameBufferLoader.tagged payload)
      (false::true::List.replicate (2*payload.length+1) false ++ [false])
    StatusRel (run (FrameBufferHandoff.program (FrameBufferSeek.program (program p)))
        (initial (canonical payload))
        (FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2+(4+fuel))))
      (shiftStatus 74 (run p ((if bit then 1 else 0),out) fuel)) := by
  dsimp only
  have hv := program_valid p hp hlen
  have h := FrameBufferSeek.blank_start_then_continue (program p) hv (bit::rest) (4+fuel)
  have hs := probe_bit_then_continue p hp hlen false bit (FrameBufferLoader.tagged rest)
    (true::List.replicate (2*(bit::rest).length+1) false ++ [false]) fuel
  simp only [FrameBufferLoader.tagged_cons] at h
  simp only [List.cons_append] at h hs ⊢
  rw [hs] at h
  have hcompose (s : Status) : shiftStatus 66 (shiftStatus 8 s) = shiftStatus 74 s := by
    cases s with
    | none => rfl
    | some v => cases v <;> simp [shiftStatus,shiftConfig] <;> omega
  rw [hcompose] at h
  exact h

theorem status_trans (a b c : Status) (hab : StatusRel a b) (hbc : StatusRel b c) : StatusRel a c := by
  cases a with
  | none =>
    cases b with
    | none => simpa [StatusRel] using hbc
    | some bv => cases bv <;> simp [StatusRel] at hab
  | some av =>
    cases av with
    | inl x =>
      cases b with
      | none => simp [StatusRel] at hab
      | some bv => cases bv with
        | inr y => simp [StatusRel] at hab
        | inl y =>
          cases c with
          | none => simp [StatusRel] at hbc
          | some cv => cases cv with
            | inr z => simp [StatusRel] at hbc
            | inl z => exact hab.trans hbc
    | inr x =>
      cases b with
      | none => simp [StatusRel] at hab
      | some bv => cases bv with
        | inl y => simp [StatusRel] at hab
        | inr y =>
          cases c with
          | none => simp [StatusRel] at hbc
          | some cv => cases cv with
            | inl z => simp [StatusRel] at hbc
            | inr z => exact ⟨hab.1.trans hbc.1,hab.2.trans hbc.2⟩

/-- The zero-length frame reaches the exhausted continuation even though its
two sentinel cells are implicit blanks rather than stored list elements. -/
theorem blank_start_empty (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length)
    (fuel : Nat) :
    let out := tapeAt [] (false::true::List.replicate 1 false ++ [false])
    StatusRel (run (FrameBufferHandoff.program (FrameBufferSeek.program (program p)))
        (initial (canonical []))
        (FrameBufferBlankStart.elapsed []+2+(2*0+2+(4+fuel))))
      (shiftStatus 74 (run p (2,out) fuel)) := by
  dsimp only
  let right := false::true::List.replicate 1 false ++ [false]
  let raw := tapeAt [] right
  let padded := tapeAt [false,false] right
  have hpad : TapeRel raw padded := by
    simpa [raw,padded] using FrameBufferBlankStart.pad_left [] right 2
  have hv := program_valid p hp hlen
  have hstart := FrameBufferSeek.blank_start_then_continue (program p) hv [] (4+fuel)
  change StatusRel (run (FrameBufferHandoff.program (FrameBufferSeek.program (program p)))
      (initial (canonical [])) (FrameBufferBlankStart.elapsed []+2+(2*0+2+(4+fuel))))
    (shiftStatus 66 (run (program p) (0,raw) (4+fuel))) at hstart
  have hprobe := run_related (program p) (0,raw) (0,padded) rfl hpad (4+fuel)
  have hend := probe_end_then_continue p hp hlen false []
    (true::List.replicate 1 false ++ [false]) fuel
  change run (program p) (0,padded) (4+fuel) = _ at hend
  rw [hend] at hprobe
  have hpadded := run_related p (2,padded) (2,raw) rfl hpad.symm fuel
  have hcompose (s : Status) : shiftStatus 66 (shiftStatus 8 s) = shiftStatus 74 s := by
    cases s with
    | none => rfl
    | some v => cases v <;> simp [shiftStatus,shiftConfig] <;> omega
  have h1 := FrameBufferHandoff.shift_status_related 66 _ _ hprobe
  rw [hcompose] at h1
  have h2 := FrameBufferHandoff.shift_status_related 74 _ _ hpadded
  exact status_trans _ _ _ (status_trans _ _ _ hstart h1) h2

theorem probe_bound (payload : List Bool) :
    FrameBufferBlankStart.elapsed payload+2+(2*payload.length+2+4) ≤
      payload.length*(12*payload.length+37)+18 := by
  have h := FrameBufferSeek.seek_bound payload
  omega

end Shared.PNP.Record285.FramePairProbe
