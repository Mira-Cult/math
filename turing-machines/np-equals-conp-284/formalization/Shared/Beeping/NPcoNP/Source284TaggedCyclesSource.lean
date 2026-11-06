import Shared.Beeping.NPcoNP.Source284EncoderFirstSelection
import Shared.Codes.FiniteProgramTaggedLoop

/-! A finite tagged-buffer serializer loop, compiled to the numeric relative
source. The loop handles a specified finite number of source bits and has a
quadratic step bound. The finite run is insensitive to arbitrary high source
tape data outside its prepared window. Establishing that window, detecting the
end of the self-delimited body, and removing buffer tags remain separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284TaggedCyclesSource

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost maxWord)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284BitWindow (agree_mono)
open Shared.Beeping.NPcoNP.Source284CompileRecords (compile codeState)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)

/-- Appending virtual blank cells does not change a numeric tape half. -/
theorem value_append_blanks (xs : List Bool) (n : Nat) :
    Source284FiniteTapeStep.value (xs ++ List.replicate n false) = Source284FiniteTapeStep.value xs := by
  induction xs with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.nil_append,Source284FiniteTapeStep.value] at ih
      change Source284FiniteTapeStep.value (false::List.replicate n false) = 0
      simp [Source284FiniteTapeStep.value,Source284FiniteTapeStep.digit,ih]
  | cons b bs ih => simp [Source284FiniteTapeStep.value,ih]

/-- Blank-equivalent finite tapes have exactly the same two source numerals,
for either orientation. -/
theorem represented_tapeRel (a b : Tape) (rev : Bool) (state : Nat) (h : TapeRel a b) :
    represented a rev state = represented b rev state := by
  rcases a with ⟨al,ah,ar⟩
  rcases b with ⟨bl,bh,br⟩
  have hh : ah = bh := congrArg Turing.Tape.head h
  have hl : Turing.ListBlank.mk al = Turing.ListBlank.mk bl := congrArg Turing.Tape.left h
  have hr : Turing.ListBlank.mk ar = Turing.ListBlank.mk br := congrArg Turing.Tape.right h
  have hle : Turing.BlankRel al bl := Quotient.exact hl
  have hre : Turing.BlankRel ar br := Quotient.exact hr
  have hvl : Source284FiniteTapeStep.value al = Source284FiniteTapeStep.value bl := by
    rcases hle with ⟨n,rfl⟩ | ⟨n,rfl⟩
    · exact (value_append_blanks _ _).symm
    · exact value_append_blanks _ _
  have hvr : Source284FiniteTapeStep.value ar = Source284FiniteTapeStep.value br := by
    rcases hre with ⟨n,rfl⟩ | ⟨n,rfl⟩
    · exact (value_append_blanks _ _).symm
    · exact value_append_blanks _ _
  cases rev <;> simp [represented,hh,hvl,hvr]

/-- Numeric source simulation of all finite tagged-buffer cycles. The input
window includes the requested output window plus the actual finite run cost.
No assumption is made about higher numeric tape bits. -/
theorem cycles_source_window (zero one remaining : List Bool) (b : Bool)
    (xs L : List Bool) (rev₀ : Bool) (k : Nat) (c : Source284Relative.Config)
    (hw : Window (k+totalCost zero one remaining b xs) c
      (represented (canonical (remaining++L) b xs).2 rev₀ (codeState 0 rev₀))) :
    ∃ tape rev,
      Window k (Source284Relative.run (compile (Shared.Codes.FiniteProgramTaggedLoop.program zero one)) c
        (totalCost zero one remaining b xs)) (represented tape rev (codeState 0 rev)) ∧
      TapeRel tape (canonical L (result zero one remaining b xs).1
        (result zero one remaining b xs).2).2 := by
  let program := Shared.Codes.FiniteProgramTaggedLoop.program zero one
  let initial := canonical (remaining++L) b xs
  let cost := totalCost zero one remaining b xs
  have hv : valid program = true := Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one
  have hn : 0 < program.length := by
    cases hp : program with
    | nil => simp [hp,valid] at hv
    | cons a as => simp
  obtain ⟨d,hd,hq,htape⟩ := Shared.Codes.FiniteProgramTaggedLoop.cycles
    zero one remaining b xs L initial rfl rfl
  have hrel := Source284FiniteProgramRun.run_related program
    (Source284FiniteProgramRun.closed_of_valid program hv) 0 initial.2 rev₀ hn cost
  have he : (0,initial.2) = initial := by rfl
  rw [he,hd] at hrel
  rcases d with ⟨q,tape⟩
  change q = 0 at hq
  subst q
  have hex := Source284EncoderSourceWindow.live_invert program 0 tape _ hrel
  obtain ⟨rev,hr⟩ := hex
  have hwin := Source284Relative.run_window (compile program) cost k c
    (represented initial.2 rev₀ (codeState 0 rev₀)) hw
  rw [hr] at hwin
  exact ⟨tape,rev,hwin,htape⟩

/-- A content-independent quadratic budget suffices for the same source
run. The input still needs a constructed window of that size. -/
theorem cycles_source_polynomial_window (zero one remaining : List Bool) (b : Bool)
    (xs L : List Bool) (rev₀ : Bool) (k : Nat) (c : Source284Relative.Config)
    (hw : Window (k + remaining.length *
      (16*(xs.length+remaining.length*(1+maxWord zero one))+16*maxWord zero one+31)) c
      (represented (canonical (remaining++L) b xs).2 rev₀ (codeState 0 rev₀))) :
    ∃ tape rev,
      Window k (Source284Relative.run (compile (Shared.Codes.FiniteProgramTaggedLoop.program zero one)) c
        (totalCost zero one remaining b xs)) (represented tape rev (codeState 0 rev)) ∧
      TapeRel tape (canonical L (result zero one remaining b xs).1
        (result zero one remaining b xs).2).2 := by
  have hb := Shared.Codes.FiniteProgramTaggedLoop.totalCost_bound zero one remaining b xs
  apply cycles_source_window zero one remaining b xs L rev₀ k c
  exact ⟨hw.1,agree_mono (by omega) hw.2.1,agree_mono (by omega) hw.2.2⟩

/-- The final finite tape may be replaced by its canonical tagged-buffer
layout even though the finite evaluator used blank-equivalent lists. -/
theorem cycles_source_canonical_window (zero one remaining : List Bool) (b : Bool)
    (xs L : List Bool) (rev₀ : Bool) (k : Nat) (c : Source284Relative.Config)
    (hw : Window (k+totalCost zero one remaining b xs) c
      (represented (canonical (remaining++L) b xs).2 rev₀ (codeState 0 rev₀))) :
    ∃ rev, Window k (Source284Relative.run
      (compile (Shared.Codes.FiniteProgramTaggedLoop.program zero one)) c
      (totalCost zero one remaining b xs))
      (represented (canonical L (result zero one remaining b xs).1
        (result zero one remaining b xs).2).2 rev (codeState 0 rev)) := by
  obtain ⟨tape,rev,hw',ht⟩ := cycles_source_window zero one remaining b xs L rev₀ k c hw
  rw [represented_tapeRel tape _ rev _ ht] at hw'
  exact ⟨rev,hw'⟩

/-- Metadata bit followed by the selected fixed word, for each processed
source bit. The last head bit is not processed until another predecessor is
available. -/
def emitted (zero one : List Bool) : List Bool → Bool → List Bool
  | [], _ => []
  | p::ps, b => b::(if b then one else zero) ++ emitted zero one ps p

/-- The cyclic table's accumulated buffer has exactly the advertised word
sequence, including every metadata bit. -/
theorem result_words (zero one remaining : List Bool) (b : Bool) (xs : List Bool) :
    (result zero one remaining b xs).2 = xs ++ emitted zero one remaining b := by
  induction remaining generalizing b xs with
  | nil => simp [result,emitted]
  | cons p ps ih =>
    simp only [result,emitted]
    rw [ih]
    simp [Shared.Codes.FiniteProgramTaggedLoop.output,List.append_assoc]

/-- The bits processed by a fixed number of cycles, in their actual scan
order. The final predecessor remains under the head. -/
def processed : List Bool → Bool → List Bool
  | [], _ => []
  | p::ps, b => b::processed ps p

theorem emitted_flatMap (zero one remaining : List Bool) (b : Bool) :
    emitted zero one remaining b =
      (processed remaining b).flatMap (fun v => v::(if v then one else zero)) := by
  induction remaining generalizing b with
  | nil => rfl
  | cons p ps ih => simp [emitted,processed,ih,List.append_assoc]

/-- For the actual encoder, each processed bit is followed by its genuine
fixed-width unmarked symbol code. The leading bit is metadata for the
existing frame-removal pass, not part of the desired serialized input. -/
theorem encoder_emitted {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (remaining : List Bool) (b : Bool) :
    emitted (Source284EncoderFirstSelection.code enc false)
      (Source284EncoderFirstSelection.code enc true) remaining b =
      (processed remaining b).flatMap (fun v => v::Source284EncoderFirstSelection.code enc v) := by
  rw [emitted_flatMap]
  congr 1
  funext v
  cases v <;> rfl

/-- The metadata-bearing sequence is exactly the framed input expected by
the existing finite metadata-removal pass. -/
theorem emitted_framed {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (remaining : List Bool) (b : Bool) :
    emitted (Source284EncoderFirstSelection.code enc false)
      (Source284EncoderFirstSelection.code enc true) remaining b =
    Shared.Codes.FiniteProgramFrameLoop.framed
      ((processed remaining b).map (fun v => (v,Source284EncoderFirstSelection.code enc v))) := by
  rw [encoder_emitted]
  generalize processed remaining b = bits
  induction bits with
  | nil => rfl
  | cons v vs ih =>
    simp [Shared.Codes.FiniteProgramFrameLoop.framed,ih]

/-- With the fixed initial marker retained, the loop output has exactly
the frame-removal pass's expected input shape. -/
theorem encoder_result_framed {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (remaining : List Bool) (b : Bool) :
    (result (Source284EncoderFirstSelection.code enc false)
      (Source284EncoderFirstSelection.code enc true) remaining b
      (Source284EncoderMarkerSeed.marker enc)).2 =
      Source284EncoderMarkerSeed.marker enc ++
        Shared.Codes.FiniteProgramFrameLoop.framed
          ((processed remaining b).map (fun v => (v,Source284EncoderFirstSelection.code enc v))) := by
  rw [result_words,emitted_framed]

theorem code_length {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width) (b : Bool) :
    (Source284EncoderFirstSelection.code enc b).length = width := by
  simp [Source284EncoderFirstSelection.code]

theorem maxWord_encoder {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width) :
    maxWord (Source284EncoderFirstSelection.code enc false)
      (Source284EncoderFirstSelection.code enc true) = width := by
  simp [maxWord,code_length]

/-- A fully explicit quadratic source-step budget for the encoder's
fixed-width symbol codes. The prepared window is still a hypothesis. -/
theorem encoder_cycles_window {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (remaining : List Bool) (b : Bool) (xs L : List Bool) (rev₀ : Bool)
    (k : Nat) (c : Source284Relative.Config)
    (hw : Window (k + remaining.length *
      (16*(xs.length+remaining.length*(1+width))+16*width+31)) c
      (represented (canonical (remaining++L) b xs).2 rev₀ (codeState 0 rev₀))) :
    ∃ tape rev,
      Window k (Source284Relative.run
        (compile (Shared.Codes.FiniteProgramTaggedLoop.program
          (Source284EncoderFirstSelection.code enc false) (Source284EncoderFirstSelection.code enc true))) c
        (totalCost (Source284EncoderFirstSelection.code enc false)
          (Source284EncoderFirstSelection.code enc true) remaining b xs))
        (represented tape rev (codeState 0 rev)) ∧
      TapeRel tape (canonical L
        (result (Source284EncoderFirstSelection.code enc false)
          (Source284EncoderFirstSelection.code enc true) remaining b xs).1
        (result (Source284EncoderFirstSelection.code enc false)
          (Source284EncoderFirstSelection.code enc true) remaining b xs).2).2 := by
  apply cycles_source_polynomial_window _ _ remaining b xs L rev₀ k c
  simpa [maxWord_encoder] using hw

/-- Every cycle is strictly positive, preventing an infinite sequence of
zero-cost abstract updates. -/
theorem totalCost_progress (zero one remaining : List Bool) (b : Bool) (xs : List Bool) :
    31*remaining.length ≤ totalCost zero one remaining b xs := by
  induction remaining generalizing b xs with
  | nil => simp [totalCost]
  | cons p ps ih =>
    simp only [totalCost,List.length_cons]
    have h := ih p (Shared.Codes.FiniteProgramTaggedLoop.output zero one b xs)
    simp only [Shared.Codes.FiniteProgramTaggedLoop.cost]
    omega

namespace Fixtures
example : processed [true,false] false = [false,true] := by decide +kernel
example : emitted [false] [true] [true,false] false = [false,false,true,true] := by decide +kernel
example : 31*2 ≤ totalCost [false] [true] [true,false] false [] := by
  simpa using totalCost_progress [false] [true] [true,false] false []
end Fixtures

end Shared.Beeping.NPcoNP.Source284TaggedCyclesSource
