import Shared.Beeping.NPcoNP.Source284RelativeTableDecode
import Shared.Beeping.NPcoNP.Source284Comparison
import Shared.Beeping.NPcoNP.Source284WindowRewind
import Shared.Beeping.NPcoNP.Source284ScratchScanner

/-! A finite two-step entry wrapper accepts every empty parsed prefix in
one step and otherwise resumes any given source program on unchanged tapes.
It does not decide that program's termination. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284EmptyPrefixWrapper

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)

def table (emptyValue : Bool) (original : Nat → Bool → Row) (q : Nat) (read : Bool) : Row :=
  if q=0 then if read then ⟨true,true,some 1⟩ else ⟨false,false,if emptyValue then none else some 1⟩
  else if q=1 then ⟨read,true,some 2⟩
  else shiftRow 2 (original (q-2) read)

theorem closed (emptyValue : Bool) (n : Nat) (original : Nat → Bool → Row) (hn : 0 < n) (hv : Closed n original) :
    Closed (2+n) (table emptyValue original) := by
  intro q hq b q' hnext
  by_cases hs : q<2
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 2 (original (q-2) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega] using hnext
    cases ht : (original (q-2) b).next with
    | none => simp [shiftRow,ht] at he
    | some r =>
      have hr := hv (q-2) (by omega) b r ht
      simp [shiftRow,ht] at he
      subst q'
      omega

theorem relocated_run (emptyValue : Bool) (original : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table emptyValue original) (shiftConfig 2 c) fuel = shiftConfig 2 (run original c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,ih]
    cases hc : run original c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        simp only [shiftConfig,Option.map_some,step,table,show 2+q ≠ 0 by omega,
          show 2+q ≠ 1 by omega,↓reduceIte,show 2+q-2=q by omega,shiftRow]
        split <;> rfl

/-- Both turns preserve the complete input and certificate halves. -/
theorem positive_setup (emptyValue : Bool) (original : Nat → Bool → Row) (input certificate : Nat) (hodd : input%2=1) :
    run (table emptyValue original) ⟨certificate,input,some 0⟩ 2 = ⟨certificate,input,some 2⟩ := by
  have hbit : input.testBit 0 = true := by simp [Nat.testBit_zero,hodd]
  have h0 : step (table emptyValue original) ⟨certificate,input,some 0⟩ = ⟨input,certificate,some 1⟩ := by
    simp [step,table,hbit,bit]
    omega
  have h1 : step (table emptyValue original) ⟨input,certificate,some 1⟩ = ⟨certificate,input,some 2⟩ := by
    apply Source284WindowRewind.generic_turn
    intro b
    simp [table]
  simp only [run,h0,h1]

def description (emptyValue : Bool) (original : Nat) : Nat :=
  encode (2+Source284RelativeTableDecode.states original)
    (table emptyValue (Source284RelativeTableDecode.table original)) 1

/-- Empty source frames accept on the first real transition, independently
of the arbitrary certificate and all higher input bits. -/
theorem empty_accepts (emptyValue : Bool) (original input certificate : Nat) (heven : input%2=0) :
    Source284Relative.accepts (description emptyValue original) input certificate 1 = emptyValue := by
  let n := Source284RelativeTableDecode.states original
  have hc := closed emptyValue n (Source284RelativeTableDecode.table original)
    (Source284RelativeTableDecode.states_positive original) (Source284RelativeTableDecode.closed original)
  have h := bounded_acceptance (2+n) (table emptyValue (Source284RelativeTableDecode.table original)) 1
    (by omega) hc input certificate 1
  change Source284Relative.accepts (description emptyValue original) input certificate 1 = _ at h
  rw [h]
  have hb : input.testBit 0 = false := by simp [Nat.testBit_zero,heven]
  cases emptyValue <;> simp [run,step,table,hb]

/-- Positive prefixes incur exactly two paid turns and then agree with the
original source program for every clock and every certificate. -/
theorem positive_accepts (emptyValue : Bool) (original input certificate fuel : Nat) (hodd : input%2=1) :
    Source284Relative.accepts (description emptyValue original) input certificate (2+fuel) =
      Source284Relative.accepts original input certificate fuel := by
  let n := Source284RelativeTableDecode.states original
  let t := Source284RelativeTableDecode.table original
  have hc := closed emptyValue n t (Source284RelativeTableDecode.states_positive original)
    (Source284RelativeTableDecode.closed original)
  have h := bounded_acceptance (2+n) (table emptyValue t) 1 (by omega) hc input certificate (2+fuel)
  change Source284Relative.accepts (description emptyValue original) input certificate (2+fuel) = _ at h
  rw [h,Source284ScratchScanner.run_add,positive_setup emptyValue t input certificate hodd]
  change (run (table emptyValue t) (shiftConfig 2 ⟨certificate,input,some 0⟩) fuel).state.isNone = _
  rw [relocated_run emptyValue]
  have hr := Source284RelativeTableDecode.reflected_acceptance original input certificate fuel
  rw [hr]
  cases hs : (run t ⟨certificate,input,some 0⟩ fuel).state <;> simp [shiftConfig,hs]

end Shared.Beeping.NPcoNP.Source284EmptyPrefixWrapper
