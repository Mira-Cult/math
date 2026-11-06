import Shared.Beeping.NPcoNP.Source284UnaryCountBits
import Shared.ComplexityBridge.TM2ListReverse
import Shared.ComplexityBridge.TM2Compose

/-! A canonical finite-TM2 implementation of the data-only binary-list
increment. The input is a raw little-endian list, including noncanonical
high zeroes. This does not prove polynomial time for the source evaluator. -/

set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284IncrementTM2

open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.Beeping.NPcoNP.Source284UnaryCountBits

inductive Stack where | input | output deriving DecidableEq
inductive Label where | scan deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.scan] (by intro l; cases l; simp)
abbrev State := Bool × Option Bool

/-- The finite control tracks carry. Each input bit is read once and its
transformed canonical three-bit list cell is prepended. -/
def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .scan => .pop .input (fun s h => (s.1,h))
      (.branch (fun s => s.2.isSome)
        (.pop .input (fun s h => (s.1,h))
          (.push .output (fun _ => false)
            (.push .output (fun s => if s.1 then !s.2.getD false else s.2.getD false)
              (.push .output (fun _ => true)
                (.pop .input (fun s _ => (s.1 && s.2.getD false,none))
                  (.goto (fun _ => .scan)))))))
        (.branch (fun s => s.1)
          (.push .output (fun _ => false)
            (.push .output (fun _ => true)
              (.push .output (fun _ => true) (.load (fun _ => (true,none)) .halt))))
          (.load (fun _ => (true,none)) .halt)))

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

def cfg (carry : Bool) (input output : List Bool) : machine.Cfg :=
  ⟨some .scan,(carry,none),stackVals input output⟩

def outBit (carry b : Bool) : Bool := if carry then !b else b
def nextCarry (carry b : Bool) : Bool := carry && b

def increment : Bool → List Bool → List Bool
  | carry, [] => if carry then [true] else []
  | carry, b :: bs => outBit carry b :: increment (nextCarry carry b) bs

theorem increment_false (xs : List Bool) : increment false xs = xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [increment, outBit, nextCarry, ih]

theorem increment_true (xs : List Bool) : increment true xs = incrementData xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [increment, outBit, nextCarry, incrementData, ih, increment_false]

theorem step_cell (carry b : Bool) (input output : List Bool) :
    machine.step (cfg carry (true::b::false::input) output) =
      some (cfg (nextCarry carry b) input (true::outBit carry b::false::output)) := by
  cases carry <;> cases b <;>
    change some (Cfg.mk _ _ _) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;>
    simp [stackVals,Function.update, outBit]

theorem step_nil (carry : Bool) (output : List Bool) :
    machine.step (cfg carry [] output) =
      some (Turing.haltList machine ((if carry then [true,true,false] else []) ++ output)) := by
  cases carry <;> change some (Cfg.mk _ _ _) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update,machine]

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

theorem scan_run (xs : List Bool) (carry : Bool) (output : List Bool) :
    runSteps machine.step (xs.length+1) (cfg carry (BitstringEncoding.bitEncode xs) output) =
      some (Turing.haltList machine
        (BitstringEncoding.bitEncode (increment carry xs).reverse ++ output)) := by
  induction xs generalizing carry output with
  | nil =>
    cases carry with
    | false => simpa [increment, runSteps, encode_cons] using step_nil false output
    | true => simpa [increment, runSteps, encode_cons] using step_nil true output
  | cons b xs ih =>
    rw [List.length_cons, show xs.length+1+1 = (xs.length+1)+1 by omega,
      encode_cons, runSteps_front, step_cell]
    have h := ih (nextCarry carry b) (true::outBit carry b::false::output)
    simpa [increment, List.reverse_cons, encode_append, encode_cons, List.append_assoc] using h

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg true input [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals]

theorem run (xs : List Bool) :
    runSteps machine.step (xs.length+1) (Turing.initList machine (BitstringEncoding.bitEncode xs)) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode (incrementData xs).reverse)) := by
  rw [initial_eq]
  simpa [increment_true] using scan_run xs true []

noncomputable def reversedMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool) (fun xs => (incrementData xs).reverse) where
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
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (incrementData xs).reverse).map id))
      simpa using h
    · simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
        Shared.ComplexityBridge.bitstring_list_encoded_length]
      omega

/-- Canonical polynomial time includes the output-order reversal and the full
encoded input size. No claim about the rest of record lookup is made. -/
theorem incrementData_isPolyTime : ComplexityTheory.IsPolyTime incrementData := by
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    (fun xs : List Bool => (incrementData xs).reverse) (List.reverse : List Bool → List Bool)
    ⟨reversedMachine⟩ Shared.ComplexityBridge.TM2ListReverse.reverse_isPolyTime
  simpa using h

end Shared.Beeping.NPcoNP.Source284IncrementTM2
