import Shared.Beeping.NPcoNP.Source284RecordBitCost
import Shared.ComplexityBridge.TM2ListReverse
import Shared.ComplexityBridge.TM2Compose

/-! A canonical finite-TM2 implementation of the binary-list decrement
used by the source record scanner.  The input is a raw little-endian list,
including noncanonical high zeroes.  This is a component of the scanner,
not a polynomial-time proof for the whole scanner or source evaluator. -/

set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284DecrementTM2

open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.Beeping.NPcoNP.Source284RecordBitCost

inductive Stack where | input | output deriving DecidableEq
inductive Label where | scan deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.scan] (by intro l; cases l; simp)
abbrev State := Bool × Option Bool

/-- The borrow is carried in the finite control; every raw input bit is read
once, and its transformed canonical three-bit list cell is prepended. -/
def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .scan => .pop .input (fun s h => (s.1,h))
      (.branch (fun s => s.2.isSome)
        (.pop .input (fun s h => (s.1,h))
          (.push .output (fun _ => false)
            (.push .output (fun s => if s.1 then !s.2.getD false else s.2.getD false)
              (.push .output (fun _ => true)
                (.pop .input (fun s _ => (s.1 && !s.2.getD false,none))
                  (.goto (fun _ => .scan)))))))
        (.load (fun _ => (true,none)) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .scan
  σ := State
  initialState := (true,none)
  m := program

def stackVals (input output : List Bool) : Stack → List Bool
  | .input => input | .output => output

def cfg (borrow : Bool) (input output : List Bool) : machine.Cfg :=
  ⟨some .scan,(borrow,none),stackVals input output⟩

def outBit (borrow b : Bool) : Bool := if borrow then !b else b
def nextBorrow (borrow b : Bool) : Bool := borrow && !b

def decrement : Bool → List Bool → List Bool
  | _, [] => []
  | borrow, b :: bs => outBit borrow b :: decrement (nextBorrow borrow b) bs

theorem decrement_false (xs : List Bool) : decrement false xs = xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [decrement, outBit, nextBorrow, ih]

theorem decrement_true (xs : List Bool) : decrement true xs = decBits xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [decrement, outBit, nextBorrow, decBits, ih, decrement_false]

theorem step_cell (borrow b : Bool) (input output : List Bool) :
    machine.step (cfg borrow (true::b::false::input) output) =
      some (cfg (nextBorrow borrow b) input (true::outBit borrow b::false::output)) := by
  cases borrow <;> cases b <;>
    change some (Cfg.mk _ _ _) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;>
    simp [stackVals,Function.update, outBit]

theorem step_nil (borrow : Bool) (output : List Bool) :
    machine.step (cfg borrow [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,machine]

theorem encode_cons (b : Bool) (xs : List Bool) :
    BitstringEncoding.bitEncode (b::xs) = true::b::false::BitstringEncoding.bitEncode xs :=
  Shared.ComplexityBridge.CircuitPairWitness.encode_cons b xs

@[simp] theorem encode_nil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl

theorem encode_append (xs ys : List Bool) :
    BitstringEncoding.bitEncode (xs ++ ys) =
      BitstringEncoding.bitEncode xs ++ BitstringEncoding.bitEncode ys := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, encode_cons, ih, List.cons_append]

theorem scan_run (xs : List Bool) (borrow : Bool) (output : List Bool) :
    runSteps machine.step (xs.length+1) (cfg borrow (BitstringEncoding.bitEncode xs) output) =
      some (Turing.haltList machine
        (BitstringEncoding.bitEncode (decrement borrow xs).reverse ++ output)) := by
  induction xs generalizing borrow output with
  | nil => simpa [decrement, runSteps] using step_nil borrow output
  | cons b xs ih =>
    rw [List.length_cons, show xs.length+1+1 = (xs.length+1)+1 by omega,
      encode_cons, runSteps_front, step_cell]
    have h := ih (nextBorrow borrow b) (true::outBit borrow b::false::output)
    simpa [decrement, List.reverse_cons, encode_append, encode_cons, List.append_assoc] using h

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg true input [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals]

theorem run (xs : List Bool) :
    runSteps machine.step (xs.length+1) (Turing.initList machine (BitstringEncoding.bitEncode xs)) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode (decBits xs).reverse)) := by
  rw [initial_eq]
  simpa [decrement_true] using scan_run xs true []

noncomputable def reversedMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool) (fun xs => (decBits xs).reverse) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X+Polynomial.C 1
  outputsFun xs := by
    refine ⟨⟨xs.length+1,?_⟩,?_⟩
    · have h := run xs
      rw [runSteps_iterate] at h
      change (fun o => o.bind machine.step)^[xs.length+1]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode xs).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (decBits xs).reverse).map id))
      simpa using h
    · simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
        Shared.ComplexityBridge.bitstring_list_encoded_length]
      omega

/-- Canonical polynomial time includes the output-order reversal and the full
encoded input size. No claim about the rest of record lookup is made. -/
theorem decBits_isPolyTime : ComplexityTheory.IsPolyTime decBits := by
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    (fun xs : List Bool => (decBits xs).reverse) (List.reverse : List Bool → List Bool)
    ⟨reversedMachine⟩ Shared.ComplexityBridge.TM2ListReverse.reverse_isPolyTime
  simpa using h

end Shared.Beeping.NPcoNP.Source284DecrementTM2
