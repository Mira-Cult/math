import Shared.Beeping.NPcoNP.Source284JoinedEncoderFinitePrefix
import Shared.Beeping.NPcoNP.Source284PackedGuardIsolation
import Shared.Beeping.NPcoNP.Source284JoinedPrefixScan

/-! A continuing finite-program run is simulated by the relative source even
when both source tape halves have arbitrary data outside a finite window. The
application to the joined encoder uses no extra TM2 input: its bound depends
only on the joined prefix. Preparing the required serialized window and
connecting the reached control to the next verifier remain separate tasks. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284EncoderSourceWindow

open Turing Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284BitWindow (agree_mono)
open Shared.Beeping.NPcoNP.Source284CompileRecords (compile codeState)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284JoinedFrames (joinedBits)
open Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2 (machine cfg)

/-- A live compiler relation determines the entire represented tape and
orientation-specific state. -/
theorem live_invert (program : Program) (q : Nat) (tape : Tape)
    (c : Source284Relative.Config)
    (h : Source284FiniteProgramRun.Related program (some (.inr (q,tape))) c) :
    ∃ rev, c = represented tape rev (codeState q rev) := by
  cases h with
  | live _ _ rev _ => exact ⟨rev,rfl⟩

/-- The source compiler simulates any continuing finite-program prefix through
an arbitrary pair of higher tape suffixes. The conclusion retains a chosen
window of the resulting represented tape as well as the exact source state. -/
theorem compiled_live_window (program : Program) (input : List Bool)
    (d k q : Nat) (tape : Tape) (c : Source284Relative.Config)
    (hv : valid program = true)
    (hrun : run program (initial input) d = some (.inr (q,tape)))
    (hw : Window (k+d) c (Source284Relative.initial (value input) 0)) :
    ∃ rev, Window k (Source284Relative.run (compile program) c d)
      (represented tape rev (codeState q rev)) := by
  have hn : 0 < program.length := by
    cases h : program with
    | nil => simp [h,valid] at hv
    | cons a as => simp
  have hrel := Source284FiniteProgramRun.run_related program
    (Source284FiniteProgramRun.closed_of_valid program hv) 0
    (initial input).2 false hn d
  have he : (0,(initial input).2) = initial input := rfl
  rw [he,hrun,Source284FiniteProgramRun.represented_initial,
    Source284FiniteTapeStep.value_eq_shared] at hrel
  have hex := live_invert program q tape _ hrel
  obtain ⟨rev,hr⟩ := hex
  have h := Source284Relative.run_window (compile program) d k c
    (Source284Relative.initial (value input) 0) hw
  rw [hr] at h
  exact ⟨rev,h⟩

/-- The required simulator input is a fixed first codeword followed by
one codeword per bit of the reversed joined body. This is the exact order
exposed by the source-prefix scan; the first marker bit is known. -/
theorem serialized_input_shape {width : Nat}
    (enc : Alphabet machine → List.Vector Bool width) (x w : List Bool) :
    inputBits machine enc (joinedBits x w) =
      (enc (true, Function.update (fun _ => none) machine.k₀ (some true))).toList ++
      (Source284JoinedPrefixScan.joinedBody x w).reverse.flatMap
        (fun b => (enc (false,Function.update (fun _ => none) machine.k₀ (some b))).toList) := by
  have hr : (joinedBits x w).reverse =
      true :: (Source284JoinedPrefixScan.joinedBody x w).reverse := by
    simp [Source284JoinedPrefixScan.joined_eq_body]
  unfold inputBits TM1BinaryPostCosts.encodedInput TM2to1.trInit
  rw [hr]
  simp
  rw [← List.map_reverse,List.flatMap_map]

/-- The scanned tape exposes precisely the bit sequence consumed by the
serialization formula, above an arbitrary untouched higher suffix. -/
theorem scanned_body_layout (continuation : Nat → Bool → Source284TableEncode.Row)
    (x w : List Bool) (left tail : Nat) :
    Source284TableRun.run (Source284JoinedPrefixScan.table continuation)
      ⟨left,Source284LoaderAlgebra.stack (joinedBits x w) tail,some 0⟩
      (joinedBits x w).length =
    ⟨2*tail,Source284LoaderAlgebra.stack
      (Source284JoinedPrefixScan.joinedBody x w).reverse left,some 7⟩ := by
  rw [Source284JoinedPrefixScan.scan,Source284LoaderAlgebra.pushed_eq_stack]

/-- The number of serialized bits is linear in the two payload lengths. -/
theorem serialized_input_length {width : Nat}
    (enc : Alphabet machine → List.Vector Bool width) (x w : List Bool) :
    (inputBits machine enc (joinedBits x w)).length =
      width*(2*x.length+2*w.length+6) := by
  rw [inputBits_length,Source284JoinedFrames.joined_length]
  rw [Nat.max_eq_left (by omega)]

/-- A single valid finite program has a fixed handoff control and, once its
serialized TM2 input is prepared on a sufficiently large source window, reaches
that control in a prefix-dependent polynomial number of source transitions.
The high tape bits are unrestricted. This does not construct the window. -/
theorem encoder_source_window :
    letI := machine.kFin
    letI := Source284JoinedEncoderFinitePrefix.alphabet
    letI : Inhabited machine.Λ := ⟨machine.main⟩
    ∃ (width : Nat) (enc : Alphabet machine → List.Vector Bool width)
      (dec : List.Vector Bool width → Alphabet machine)
      (hblank : enc default = List.Vector.replicate width false)
      (program : Program) (clock : Polynomial Nat) (q : Nat),
      (∀ a, dec (enc a) = a) ∧ valid program = true ∧ q < program.length ∧
      ∀ (x w : List Bool) (k : Nat) (c : Source284Relative.Config),
        let bits := joinedBits x w
        let last := cfg .done none [] [] (BitstringEncoding.bitEncode (bits,([] : List Bool)))
        Window (k+clock.eval bits.length) c
          (Source284Relative.initial (value (inputBits machine enc bits)) 0) →
        ∃ d tape' mid rev,
          2*bits.length+1 ≤ d ∧ d ≤ clock.eval bits.length ∧
          TM2to1.TrCfg last mid ∧
          TM0FiniteProgram.tape tape' =
            (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr machine.m))
              (TM1to1.trCfg enc hblank mid)).Tape ∧
          Window k (Source284Relative.run (compile program) c d)
            (represented tape' rev (codeState q rev)) := by
  letI := machine.kFin
  letI := Source284JoinedEncoderFinitePrefix.alphabet
  letI : Inhabited machine.Λ := ⟨machine.main⟩
  obtain ⟨width,enc,dec,hblank,program,clock,q,hinv,hvalid,hq,hprefix⟩ :=
    Source284JoinedEncoderFinitePrefix.encoder_finite_fixed_handoff
  refine ⟨width,enc,dec,hblank,program,clock,q,hinv,hvalid,hq,?_⟩
  intro x w k c
  dsimp only
  intro hw
  obtain ⟨d,tape',mid,hdlo,hdhi,hrel,htape,hrun⟩ := hprefix x w []
  simp only [List.append_nil] at hdlo hdhi hrel htape hrun
  have hw' : Window (k+d) c
      (Source284Relative.initial (value (inputBits machine enc (joinedBits x w))) 0) := by
    exact ⟨hw.1,agree_mono (by omega) hw.2.1,agree_mono (by omega) hw.2.2⟩
  obtain ⟨rev,hr⟩ := compiled_live_window program
    (inputBits machine enc (joinedBits x w)) d k q tape' c hvalid hrun hw'
  exact ⟨d,tape',mid,rev,hdlo,hdhi,hrel,htape,hr⟩

namespace Fixtures

def continuing : Program := [((false,true,0,0),(false,true,0,0))]

/-- The untouched one bits outside the two-cell initial window cannot
change a one-step continuing handoff. -/
example : ∃ rev, Window 1 (Source284Relative.run (compile continuing) ⟨4,4,1⟩ 1)
    (represented ([false],false,[]) rev (codeState 0 rev)) := by
  apply compiled_live_window continuing [] 1 1 0 ([false],false,[]) ⟨4,4,1⟩
  · decide +kernel
  · decide +kernel
  · change 1 = 1 ∧ 4 % 4 = 0 ∧ 4 % 4 = 0
    decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284EncoderSourceWindow
