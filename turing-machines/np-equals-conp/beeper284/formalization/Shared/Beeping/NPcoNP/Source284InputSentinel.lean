import Shared.Beeping.NPcoNP.Source284InputPrefixLink

/-! Four paid source transitions reserve a `00` boundary beside the raw
input, saving the overwritten two certificate bits in one of four continuing
control states. This is preparation for a self-delimiting return, not yet a
complete scanner, packed-window loader, or physical machine. -/
namespace Shared.Beeping.NPcoNP.Source284InputSentinel

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284WitnessScanner (lowbit_value)

/-- Eight prefix states, followed by the continuation shifted by eight.
The first four continuation states carry the original two low certificate
bits in little-endian order. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨false,false,some (2+bit b)⟩
  else if q < 4 then ⟨false,true,some (4+(q-2)+2*bit b)⟩
  else if q < 8 then ⟨b,false,some (q+4)⟩
  else shiftRow 8 (continuation (q-8) b)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (8+states) (table continuation) 1

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 4 ≤ states) (hv : Closed states continuation) : Closed (8+states) (table continuation) := by
  intro q hq b q' hnext
  unfold table at hnext
  split_ifs at hnext with h0 h1 h2 h3
  · simp only [Option.some.injEq] at hnext; omega
  · cases b <;> simp [bit] at hnext <;> omega
  · cases b <;> simp [bit] at hnext <;> omega
  · simp only [Option.some.injEq] at hnext; omega
  · have hq0 : q-8 < states := by omega
    cases ht : (continuation (q-8) b).next with
    | none => simp [shiftRow,ht] at hnext
    | some target =>
      have hh := hv (q-8) hq0 b target ht
      simp [shiftRow,ht] at hnext
      subst q'
      omega

theorem turn_to_certificate (continuation : Nat → Bool → Row) (input certificate : Nat) :
    step (table continuation) ⟨certificate,input,some 0⟩ = ⟨input,certificate,some 1⟩ := by
  simp only [step,table,↓reduceIte]
  rw [lowbit_value]
  congr 1 <;> omega

theorem clear_first (continuation : Nat → Bool → Row) (input certificate : Nat) :
    step (table continuation) ⟨input,certificate,some 1⟩ =
      ⟨2*input,certificate/2,some (2+certificate%2)⟩ := by
  simp [step,table,bit,Nat.testBit_zero]
  split <;> omega

theorem clear_second (continuation : Nat → Bool → Row) (input certificate : Nat) :
    step (table continuation) ⟨2*input,certificate/2,some (2+certificate%2)⟩ =
      ⟨2*(certificate/4),2*input,some (4+certificate%2+2*((certificate/2)%2))⟩ := by
  have hm : certificate%2 < 2 := Nat.mod_lt certificate (by decide)
  have hmod : certificate%2 = 0 ∨ certificate%2 = 1 := by omega
  rcases hmod with h | h <;>
    simp [step,table,bit,Nat.testBit_zero,Nat.div_div_eq_div_mul,h] <;>
    split <;> simp_all <;> congr 1 <;> omega

theorem return_to_input (continuation : Nat → Bool → Row) (input certificate : Nat) :
    step (table continuation)
      ⟨2*(certificate/4),2*input,some (4+certificate%2+2*((certificate/2)%2))⟩ =
      ⟨4*(certificate/4),input,some (8+certificate%4)⟩ := by
  have hm0 : certificate%2 < 2 := Nat.mod_lt certificate (by decide)
  have hm1 : (certificate/2)%2 < 2 := Nat.mod_lt _ (by decide)
  have h0 : certificate%2 = 0 ∨ certificate%2 = 1 := by omega
  have h1 : (certificate/2)%2 = 0 ∨ (certificate/2)%2 = 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    simp [step,table,bit,Nat.testBit_zero,h0,h1] <;> congr 1 <;> omega

/-- The raw halves are transformed in exactly four paid transitions. The
continuation state stores the certificate modulo four; its higher bits and
all input bits remain on tape. -/
theorem prepare (continuation : Nat → Bool → Row) (input certificate : Nat) :
    run (table continuation) ⟨certificate,input,some 0⟩ 4 =
      ⟨4*(certificate/4),input,some (8+certificate%4)⟩ := by
  simp only [run,turn_to_certificate,clear_first,clear_second,return_to_input]

/-- The original certificate is recovered from the zero-ended half and the
four-way control mode. This is arithmetic recovery, not a return routine. -/
theorem certificate_recovered (certificate : Nat) :
    4*(certificate/4)+certificate%4 = certificate := by omega

theorem cleared_low_bits (certificate : Nat) : 4*(certificate/4) % 4 = 0 := by simp

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (8+q) b = shiftRow 8 (continuation q b) := by
  have h1 : 8+q ≠ 1 := by omega
  have h4 : ¬ 8+q < 4 := by omega
  simp [table,h1,h4]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 8 c) = shiftConfig 8 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 8 c) clock = shiftConfig 8 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The actual encoded source evaluator performs the four transitions. -/
theorem source_prepare (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial input certificate) 4 =
      ⟨4*(certificate/4),input,active (8+certificate%4)⟩ := by
  have hvalid : Valid (8+states) ⟨certificate,input,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    omega
  have h := run_toSource (8+states) (table continuation) 1
    ⟨certificate,input,some 0⟩ (closed states continuation hn hv) hvalid 4
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial input certificate) 4 = _ at h
  rw [h,prepare]
  rfl

/-- The four distinct entry modes continue in the supplied finite table;
the setup and all continuation steps are accounted for by the source clock. -/
theorem source_after_prepare (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate clock : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.accepts (description states continuation) input certificate (4+clock) =
      ((Source284Relative.run (encode states continuation 1)
        ⟨4*(certificate/4),input,active (certificate%4)⟩ clock).state == 0) := by
  have hm : certificate%4 < states := by
    have h := Nat.mod_lt certificate (by decide : 0 < 4)
    omega
  let c : Config := ⟨4*(certificate/4),input,some (certificate%4)⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hm
  have h1 : Valid (8+states) (shiftConfig 8 c) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr1 := run_toSource (8+states) (table continuation) 1 (shiftConfig 8 c)
    (closed states continuation hn hv) h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run (description states continuation)
    ⟨4*(certificate/4),input,active (8+certificate%4)⟩ clock = _ at hr1
  change Source284Relative.run (encode states continuation 1)
    ⟨4*(certificate/4),input,active (certificate%4)⟩ clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_prepare states continuation input certificate hn hv,hr1,hr0,relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

-- All four saved-bit modes, with a nonzero higher certificate bit.
example (continuation : Nat → Bool → Row) (input : Nat) :
    run (table continuation) ⟨4,input,some 0⟩ 4 = ⟨4,input,some 8⟩ := by
  simpa using prepare continuation input 4
example (continuation : Nat → Bool → Row) (input : Nat) :
    run (table continuation) ⟨5,input,some 0⟩ 4 = ⟨4,input,some 9⟩ := by
  simpa using prepare continuation input 5
example (continuation : Nat → Bool → Row) (input : Nat) :
    run (table continuation) ⟨6,input,some 0⟩ 4 = ⟨4,input,some 10⟩ := by
  simpa using prepare continuation input 6
example (continuation : Nat → Bool → Row) (input : Nat) :
    run (table continuation) ⟨7,input,some 0⟩ 4 = ⟨4,input,some 11⟩ := by
  simpa using prepare continuation input 7

end Shared.Beeping.NPcoNP.Source284InputSentinel
