import Shared.Codes.BinaryAdditionCanonical
import Shared.ComplexityBridge.CNFBinaryIncrement
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false

/-! A finite TM2 ripple adder. Its two binary inputs are explicit stack
boundaries; serialization and canonical normalization are separate. -/
namespace Shared.ComplexityBridge.CNFBinaryAdd
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.Codes.BinaryAddition

inductive Stack where | left | right | scratch | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.left,.right,.scratch,.output] (by intro s; cases s <;> simp)
inductive Label where | readLeft | readRight | restore deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.readLeft,.readRight,.restore] (by intro l; cases l <;> simp)
abbrev State := Bool × Option Bool × Option Bool

def digit (s : State) : Bool := sumBit (s.2.1.getD false) (s.2.2.getD false) s.1
def carry (s : State) : Bool := carryBit (s.2.1.getD false) (s.2.2.getD false) s.1
def hasDigit (s : State) : Bool := s.2.1.isSome || s.2.2.isSome

def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .readLeft => .pop .left (fun s h => (s.1,h,none)) (.goto (fun _ => .readRight))
  | .readRight => .pop .right (fun s h => (s.1,s.2.1,h))
      (.branch hasDigit
        (.push .scratch digit (.load (fun s => (carry s,none,none)) (.goto (fun _ => .readLeft))))
        (.branch (fun s => s.1)
          (.push .scratch (fun _ => true) (.load (fun _ => (false,none,none)) (.goto (fun _ => .restore))))
          (.load (fun _ => (false,none,none)) (.goto (fun _ => .restore)))))
  | .restore => .pop .scratch (fun s h => (s.1,s.2.1,h))
      (.branch (fun s => s.2.2.isSome)
        (.push .output (fun s => s.2.2.getD false) (.goto (fun _ => .restore)))
        (.load (fun _ => (false,none,none)) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .left
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .readLeft
  σ := State
  initialState := (false,none,none)
  m := program

def stackVals (a b scratch output : List Bool) : Stack → List Bool
  | .left => a | .right => b | .scratch => scratch | .output => output

def cfg (l : Label) (s : State) (a b scratch output : List Bool) : machine.Cfg :=
  ⟨some l,s,stackVals a b scratch output⟩

theorem readLeft (c : Bool) (as bs scratch out : List Bool) :
    machine.step (cfg .readLeft (c,none,none) as bs scratch out) =
      some (cfg .readRight (c,as.head?,none) as.tail bs scratch out) := by
  cases as with
  | nil =>
    change some (Cfg.mk (some Label.readRight) (c,none,none)
      (Function.update (stackVals [] bs scratch out) .left [])) = _
    congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]
  | cons a as =>
    change some (Cfg.mk (some Label.readRight) (c,some a,none)
      (Function.update (stackVals (a::as) bs scratch out) .left as)) = _
    congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem readRight_digit (c : Bool) (as bs scratch out : List Bool)
    (h : as ≠ [] ∨ bs ≠ []) :
    machine.step (cfg .readRight (c,as.head?,none) as.tail bs scratch out) =
      some (cfg .readLeft
        (carryBit (as.head?.getD false) (bs.head?.getD false) c,none,none) as.tail bs.tail
        (sumBit (as.head?.getD false) (bs.head?.getD false) c::scratch) out) := by
  cases as with
  | nil =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      change some (Cfg.mk (some Label.readLeft) (carryBit false b c,none,none)
        (Function.update (Function.update (stackVals [] (b::bs) scratch out) .right bs)
          .scratch (sumBit false b c::scratch))) = _
      congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]
  | cons a as =>
    cases bs with
    | nil =>
      change some (Cfg.mk (some Label.readLeft) (carryBit a false c,none,none)
        (Function.update (Function.update (stackVals as [] scratch out) .right [])
          .scratch (sumBit a false c::scratch))) = _
      congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]
    | cons b bs =>
      change some (Cfg.mk (some Label.readLeft) (carryBit a b c,none,none)
        (Function.update (Function.update (stackVals as (b::bs) scratch out) .right bs)
          .scratch (sumBit a b c::scratch))) = _
      congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem readRight_end (c : Bool) (scratch out : List Bool) :
    machine.step (cfg .readRight (c,none,none) [] [] scratch out) =
      some (cfg .restore (false,none,none) [] [] ((if c then [true] else [])++scratch) out) := by
  cases c with
  | false =>
    change some (Cfg.mk (some Label.restore) (false,none,none)
      (Function.update (stackVals [] [] scratch out) .right [])) = _
    congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]
  | true =>
    change some (Cfg.mk (some Label.restore) (false,none,none)
      (Function.update (Function.update (stackVals [] [] scratch out) .right []) .scratch (true::scratch))) = _
    congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (c : Bool) (a : Option Bool) (b : Bool) (scratch out : List Bool) :
    machine.step (cfg .restore (c,a,none) [] [] (b::scratch) out) =
      some (cfg .restore (c,a,some b) [] [] scratch (b::out)) := by
  change some (Cfg.mk (some Label.restore) (c,a,some b)
    (Function.update (Function.update (stackVals [] [] (b::scratch) out) .scratch scratch) .output (b::out))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons_any (s : State) (b : Bool) (scratch out : List Bool) :
    machine.step (cfg .restore s [] [] (b::scratch) out) =
      some (cfg .restore (s.1,s.2.1,some b) [] [] scratch (b::out)) := by
  rcases s with ⟨c,a,old⟩
  change some (Cfg.mk (some Label.restore) (c,a,some b)
    (Function.update (Function.update (stackVals [] [] (b::scratch) out) .scratch scratch) .output (b::out))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_end (s : State) (out : List Bool) :
    machine.step (cfg .restore s [] [] [] out) = some (Turing.haltList machine out) := by
  rcases s with ⟨c,a,b⟩
  change some (Cfg.mk (none : Option Label) ((false,none,none) : State)
    (Function.update (stackVals [] [] [] out) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,machine]

theorem restore_run (scratch out : List Bool) (s : State) :
    runSteps machine.step (scratch.length+1) (cfg .restore s [] [] scratch out) =
      some (Turing.haltList machine (scratch.reverse++out)) := by
  induction scratch generalizing out s with
  | nil => exact restore_end s out
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons_any]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::out) (s.1,s.2.1,some b)


theorem twoDigit (c : Bool) (as bs scratch out : List Bool) (h : as ≠ [] ∨ bs ≠ []) :
    runSteps machine.step 2 (cfg .readLeft (c,none,none) as bs scratch out) =
      some (cfg .readLeft
        (carryBit (as.head?.getD false) (bs.head?.getD false) c,none,none) as.tail bs.tail
        (sumBit (as.head?.getD false) (bs.head?.getD false) c::scratch) out) := by
  rw [show 2 = 1+1 by omega,runSteps_front,readLeft]
  simp only [Option.bind_some]
  rw [runSteps_front,readRight_digit c as bs scratch out h]
  rfl

theorem twoEnd (c : Bool) (scratch out : List Bool) :
    runSteps machine.step 2 (cfg .readLeft (c,none,none) [] [] scratch out) =
      some (cfg .restore (false,none,none) [] [] ((if c then [true] else [])++scratch) out) := by
  rw [show 2 = 1+1 by omega,runSteps_front,readLeft]
  simp only [Option.bind_some,List.head?_nil,List.tail_nil]
  rw [runSteps_front,readRight_end]
  rfl

/-- One pair of TM2 blocks handles each bit position; a final pair detects
    exhaustion and emits any carry. -/
theorem add_to_restore (as bs : List Bool) (c : Bool) (scratch out : List Bool) :
    runSteps machine.step (2*(max as.length bs.length)+2)
      (cfg .readLeft (c,none,none) as bs scratch out) =
      some (cfg .restore (false,none,none) [] [] ((addBits as bs c).reverse++scratch) out) := by
  induction as, bs, c using addBits.induct generalizing scratch with
  | case1 => simpa [addBits] using twoEnd true scratch out
  | case2 c hc =>
    cases c with
    | false => simpa [addBits] using twoEnd false scratch out
    | true => contradiction
  | case3 a as c ih =>
    have hd := twoDigit c (a::as) [] scratch out (Or.inl (by simp))
    have hr := ih (sumBit a false c::scratch)
    have hn : 2*(max (a::as).length ([] : List Bool).length)+2 =
        2+(2*(max as.length 0)+2) := by simp; omega
    rw [hn,runSteps_add,hd]
    simpa [addBits,List.reverse_cons,List.append_assoc] using hr
  | case4 b bs c ih =>
    have hd := twoDigit c [] (b::bs) scratch out (Or.inr (by simp))
    have hr := ih (sumBit false b c::scratch)
    have hn : 2*(max ([] : List Bool).length (b::bs).length)+2 =
        2+(2*(max 0 bs.length)+2) := by simp; omega
    rw [hn,runSteps_add,hd]
    simpa [addBits,List.reverse_cons,List.append_assoc] using hr
  | case5 a as b bs c ih =>
    have hd := twoDigit c (a::as) (b::bs) scratch out (Or.inl (by simp))
    have hr := ih (sumBit a b c::scratch)
    have hn : 2*(max (a::as).length (b::bs).length)+2 =
        2+(2*(max as.length bs.length)+2) := by simp; omega
    rw [hn,runSteps_add,hd]
    simpa [addBits,List.reverse_cons,List.append_assoc] using hr

/-- The two-stack input boundary returns the correct sum in a finite run.
    The explicit time counts complete TM2 statement blocks. -/
theorem run_add (as bs : List Bool) :
    runSteps machine.step (2*(max as.length bs.length)+2+((addBits as bs false).length+1))
      (cfg .readLeft (false,none,none) as bs [] []) =
      some (Turing.haltList machine (addBits as bs false)) := by
  rw [runSteps_add,add_to_restore]
  simpa using restore_run (addBits as bs false).reverse [] (false,none,none)

theorem run_add_bounded (as bs : List Bool) :
    ∃ n ≤ 3*(max as.length bs.length)+4,
      runSteps machine.step n (cfg .readLeft (false,none,none) as bs [] []) =
        some (Turing.haltList machine (addBits as bs false)) ∧
      Shared.Codes.BitNumeralCompare.value (addBits as bs false) =
        Shared.Codes.BitNumeralCompare.value as + Shared.Codes.BitNumeralCompare.value bs := by
  refine ⟨2*(max as.length bs.length)+2+((addBits as bs false).length+1),?_,run_add as bs,?_⟩
  · have h := addBits_length as bs false; omega
  · simpa using addBits_value as bs false

/-- For canonical natural-number input bit lists, the returned bit list has
    the numerical value of their sum. The later theorem strengthens this
    to equality with the canonical representation. -/
theorem run_numeral_sum (a b : Nat) :
    ∃ n ≤ 3*(max a.bits.length b.bits.length)+4,
      ∃ output, runSteps machine.step n
        (cfg .readLeft (false,none,none) a.bits b.bits [] []) =
          some (Turing.haltList machine output) ∧
        Shared.Codes.BitNumeralCompare.value output = a+b ∧
        output.length ≤ max a.bits.length b.bits.length+1 := by
  have h := run_add_bounded a.bits b.bits
  rcases h with ⟨n, hn, hr, hv⟩
  refine ⟨n, hn, addBits a.bits b.bits false, hr, ?_, addBits_length _ _ _⟩
  have ha : Shared.Codes.BitNumeralCompare.value a.bits = a := by
    rw [← Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits]
    exact Shared.Codes.BitNumeralCompare.value_encodeNat a
  have hb : Shared.Codes.BitNumeralCompare.value b.bits = b := by
    rw [← Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits]
    exact Shared.Codes.BitNumeralCompare.value_encodeNat b
  simpa [ha,hb] using hv

/-- Canonical natural numerals are returned in the pinned canonical encoding.
    Both inputs must already be loaded on their designated stacks. -/
theorem run_encoded_sum (a b : Nat) :
    ∃ n ≤ 3*(max a.bits.length b.bits.length)+4,
      runSteps machine.step n
        (cfg .readLeft (false,none,none) a.bits b.bits [] []) =
          some (Turing.haltList machine (a+b).bits) := by
  obtain ⟨n, hn, hr, _⟩ := run_add_bounded a.bits b.bits
  refine ⟨n, hn, ?_⟩
  simpa only [Shared.Codes.BinaryAdditionCanonical.addBits_numerals] using hr

namespace Fixtures
example : ∃ n ≤ 10, runSteps machine.step n
    (cfg .readLeft (false,none,none) [true,true] [true] [] []) =
    some (Turing.haltList machine [false,false,true]) := by
  obtain ⟨n, hn, hr, _⟩ := run_add_bounded [true,true] [true]
  exact ⟨n, hn, by simpa [addBits,sumBit,carryBit] using hr⟩
end Fixtures

end Shared.ComplexityBridge.CNFBinaryAdd
