import Shared.Codes.BitTableValidation
import Shared.ComplexityBridge.CNFNatBitMachine
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false

/-! A finite TM2 incrementer for explicitly supplied least-significant-bit-
first binary numerals. This is one component of CNF variable indexing. -/
namespace Shared.ComplexityBridge.CNFBinaryIncrement
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.Codes.BitTableValidation (increment)

inductive Stack where | input | scratch | output deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro s; cases s <;> simp)
inductive Label where | carry | copy | restore deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.carry,.copy,.restore] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .carry => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true)
          (.push .scratch (fun _ => false) (.goto (fun _ => .carry)))
          (.push .scratch (fun _ => true) (.goto (fun _ => .copy))))
        (.push .scratch (fun _ => true) (.goto (fun _ => .restore))))
  | .copy => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false) (.goto (fun _ => .copy)))
        (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.load (fun _ => none) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .carry
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem carry_one (v : Option Bool) (bits scratch out : List Bool) :
    machine.step (cfg .carry v (true::bits) scratch out) = some (cfg .carry (some true) bits (false::scratch) out) := by
  change some (Cfg.mk (some Label.carry) (some true)
    (Function.update (Function.update (stackVals (true::bits) scratch out) .input bits) .scratch (false::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem carry_zero (v : Option Bool) (bits scratch out : List Bool) :
    machine.step (cfg .carry v (false::bits) scratch out) = some (cfg .copy (some false) bits (true::scratch) out) := by
  change some (Cfg.mk (some Label.copy) (some false)
    (Function.update (Function.update (stackVals (false::bits) scratch out) .input bits) .scratch (true::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem carry_empty (v : Option Bool) (scratch out : List Bool) :
    machine.step (cfg .carry v [] scratch out) = some (cfg .restore none [] (true::scratch) out) := by
  change some (Cfg.mk (some Label.restore) (none : Option Bool)
    (Function.update (Function.update (stackVals [] scratch out) .input []) .scratch (true::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem copy_cons (v : Option Bool) (b : Bool) (bits scratch out : List Bool) :
    machine.step (cfg .copy v (b::bits) scratch out) = some (cfg .copy (some b) bits (b::scratch) out) := by
  change some (Cfg.mk (some Label.copy) (some b)
    (Function.update (Function.update (stackVals (b::bits) scratch out) .input bits) .scratch (b::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem copy_empty (v : Option Bool) (scratch out : List Bool) :
    machine.step (cfg .copy v [] scratch out) = some (cfg .restore none [] scratch out) := by
  change some (Cfg.mk (some Label.restore) (none : Option Bool) (Function.update (stackVals [] scratch out) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (scratch out : List Bool) :
    machine.step (cfg .restore v [] (b::scratch) out) = some (cfg .restore (some b) [] scratch (b::out)) := by
  change some (Cfg.mk (some Label.restore) (some b)
    (Function.update (Function.update (stackVals [] (b::scratch) out) .scratch scratch) .output (b::out))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_empty (v : Option Bool) (out : List Bool) :
    machine.step (cfg .restore v [] [] out) = some (Turing.haltList machine out) := by
  change some (Cfg.mk (none : Option Label) (none : Option Bool) (Function.update (stackVals [] [] out) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,machine]

theorem copy_run (bits scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (bits.length+1) (cfg .copy v bits scratch out) =
      some (cfg .restore none [] (bits.reverse++scratch) out) := by
  induction bits generalizing scratch v with
  | nil => exact copy_empty v scratch out
  | cons b bits ih =>
    rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,copy_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restore_run (scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v [] scratch out) =
      some (Turing.haltList machine (scratch.reverse++out)) := by
  induction scratch generalizing out v with
  | nil => exact restore_empty v out
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::out) (some b)

/-- Every input bit is consumed exactly once while carrying or copying. -/
theorem carry_run (bits scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (bits.length+1) (cfg .carry v bits scratch out) =
      some (cfg .restore none [] ((increment bits).1.reverse++scratch) out) := by
  induction bits generalizing scratch v with
  | nil => simpa [increment,runSteps] using carry_empty v scratch out
  | cons b bits ih =>
    cases b with
    | false =>
      rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,carry_zero]
      simpa [increment,List.reverse_cons,List.append_assoc] using copy_run bits (true::scratch) out (some false)
    | true =>
      rw [List.length_cons,show bits.length+1+1 = (bits.length+1)+1 by omega,runSteps_front,carry_one]
      simpa [increment,List.reverse_cons,List.append_assoc] using ih (false::scratch) (some true)

theorem initial_eq (bits : List Bool) : Turing.initList machine bits = cfg .carry none bits [] [] := by
  change Cfg.mk (some Label.carry) none _ = Cfg.mk (some Label.carry) none (stackVals bits [] [])
  congr 1; funext k; cases k <;> simp [machine,stackVals]

/-- The actual finite TM2 outputs the incremented little-endian numeral and
halts after the exact number of complete statement blocks displayed here. -/
theorem run_increment (bits : List Bool) :
    runSteps machine.step (bits.length+1+((increment bits).1.length+1)) (Turing.initList machine bits) =
      some (Turing.haltList machine (increment bits).1) := by
  rw [initial_eq,runSteps_add,carry_run]
  simpa using restore_run (increment bits).1.reverse [] none

/-- The block bound is linear in the input bit length; bit-cost simulation
and the surrounding CNF generator are separate obligations. -/
theorem run_increment_bounded (bits : List Bool) :
    ∃ n ≤ 2*bits.length+3,
      runSteps machine.step n (Turing.initList machine bits) =
        some (Turing.haltList machine (increment bits).1) := by
  refine ⟨bits.length+1+((increment bits).1.length+1),?_,run_increment bits⟩
  have h := Shared.Codes.BitTableValidation.increment_length bits
  omega


/-- For canonical binary numerals, the incremented bit list is itself the
    canonical pinned numeral encoding of the successor. -/
theorem increment_bits (n : Nat) : (increment n.bits).1 = (n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    cases b with
    | false =>
      have hn : n ≠ 0 := by intro he; have := h he; contradiction
      change (increment (2*n).bits).1 = (2*n+1).bits
      rw [Nat.bit0_bits n hn,Nat.bit1_bits]
      rfl
    | true =>
      change (increment (2*n+1).bits).1 = (2*n+1+1).bits
      rw [Nat.bit1_bits]
      simp only [increment]
      have hs : 2*n+1+1 = 2*(n+1) := by omega
      rw [hs,Nat.bit0_bits (n+1) (by omega),ih]

/-- The finite incrementer implements successor on the actual binary encoding,
with a linear bound in its bit length. -/
theorem run_encoded_successor (n : Nat) :
    ∃ steps ≤ 2*n.bits.length+3,
      runSteps machine.step steps (Turing.initList machine n.bits) =
        some (Turing.haltList machine (BitstringEncoding.bitEncode (n+1))) := by
  have h := run_increment_bounded n.bits
  rw [increment_bits] at h
  have he : BitstringEncoding.bitEncode (n+1) = (n+1).bits :=
    Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits (n+1)
  simpa [he] using h


/-- The canonical natural-number successor has a concrete polynomial-time
TM2 witness. The source and output encodings are the pinned binary encoding. -/
noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : Nat → List Bool)
    (BitstringEncoding.bitEncode : Nat → List Bool) Nat.succ where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun n := by
    let steps := n.bits.length+1+((increment n.bits).1.length+1)
    have hbound : steps ≤ 2*n.bits.length+3 := by
      have h := Shared.Codes.BitTableValidation.increment_length n.bits
      dsimp [steps]; omega
    have hr := run_increment n.bits
    rw [increment_bits] at hr
    have heout : BitstringEncoding.bitEncode (n+1) = (n+1).bits :=
      Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits (n+1)
    rw [←heout] at hr
    refine ⟨⟨steps,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      have he : BitstringEncoding.bitEncode n = n.bits :=
        Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
      change (fun o => o.bind machine.step)^[steps]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode n).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (Nat.succ n)).map id))
      rw [List.map_id,List.map_id,he]
      simpa [steps,increment_bits,←heout] using hr
    · have he : BitstringEncoding.bitEncode n = n.bits :=
        Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits n
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,he]
      exact hbound

theorem successor_isPolyTime : ComplexityTheory.IsPolyTime (Nat.succ : Nat → Nat) := ⟨timeMachine⟩

namespace Fixtures
example : (increment []).1 = [true] := rfl
example : (increment [true,true]).1 = [false,false,true] := rfl
example : ∃ n ≤ 7, runSteps machine.step n (Turing.initList machine [true,true]) =
    some (Turing.haltList machine [false,false,true]) := by
  simpa [increment] using run_increment_bounded [true,true]
end Fixtures
end Shared.ComplexityBridge.CNFBinaryIncrement
