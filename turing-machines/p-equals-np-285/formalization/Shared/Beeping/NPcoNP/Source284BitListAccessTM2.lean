import Shared.ComplexityBridge.TM2InputBitLookup
import Shared.ComplexityBridge.TM2EmptyConstant
import Shared.ComplexityBridge.TM2ListReverse

/-! Canonical polynomial-time access to the head and tail of arbitrary
Boolean lists, used for the source evaluator's finite tape halves. Empty
lists return the specified virtual-zero head and an empty tail. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284BitListAccessTM2

open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge

theorem head_isPolyTime : ComplexityTheory.IsPolyTime
    (fun xs : List Bool => xs.headD false) := by
  let zero : List Bool → Nat := fun _ => 0
  let args : List Bool → List Bool × Nat := fun xs => (xs,zero xs)
  have hi : ComplexityTheory.IsPolyTime (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args :=
    TM2GuardAllStep.pair_isPolyTime id zero hi hz
  have h := TM2Compose.isPolyTime_comp args TM2InputBitLookup.lookup ha TM2InputBitLookup.lookup_isPolyTime
  have he : (fun xs : List Bool => TM2InputBitLookup.lookup (args xs)) =
      (fun xs => xs.headD false) := by
    funext xs
    cases xs <;> simp [args, zero, TM2InputBitLookup.lookup_correct]
  rw [he] at h
  exact h

inductive Stack where | input | scratch | output deriving DecidableEq
inductive Label where | drop | copy | restore deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.drop,.copy,.restore] (by intro l; cases l <;> simp)

/-- One block discards the first encoded list cell, which has three bits;
two finite sweeps then preserve the order of the remaining raw encoding. -/
def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .drop => .pop .input (fun _ _ => none)
      (.pop .input (fun _ _ => none)
        (.pop .input (fun _ _ => none) (.goto (fun _ => .copy))))
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
  main := .drop
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

def cfg (label : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some label,v,stackVals input scratch output⟩

theorem drop_nil : machine.step (Turing.initList machine []) = some (cfg .copy none [] [] []) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [machine,stackVals,Function.update]

theorem drop_cell (b : Bool) (tail : List Bool) :
    machine.step (Turing.initList machine (true::b::false::tail)) = some (cfg .copy none tail [] []) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [machine,stackVals,Function.update]

theorem copy_cons (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .copy v (b::xs) scratch out) = some (cfg .copy (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem copy_nil (v : Option Bool) (scratch out : List Bool) :
    machine.step (cfg .copy v [] scratch out) = some (cfg .restore none [] scratch out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (scratch out : List Bool) :
    machine.step (cfg .restore v [] (b::scratch) out) = some (cfg .restore (some b) [] scratch (b::out)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (out : List Bool) :
    machine.step (cfg .restore v [] [] out) = some (Turing.haltList machine out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [machine,stackVals,Function.update]

theorem copy_run (xs scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (xs.length+1) (cfg .copy v xs scratch out) =
      some (cfg .restore none [] (xs.reverse++scratch) out) := by
  induction xs generalizing scratch v with
  | nil => simpa [runSteps] using copy_nil v scratch out
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,copy_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restore_run (scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v [] scratch out) =
      some (Turing.haltList machine (scratch.reverse++out)) := by
  induction scratch generalizing out v with
  | nil => simpa [runSteps] using restore_nil v out
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::out) (some b)

theorem encoded_cons (b : Bool) (xs : List Bool) :
    BitstringEncoding.bitEncode (b::xs) = true::b::false::BitstringEncoding.bitEncode xs :=
  Shared.ComplexityBridge.CircuitPairWitness.encode_cons b xs

theorem run_tail (xs : List Bool) :
    runSteps machine.step (2*(BitstringEncoding.bitEncode xs.tail).length+3)
      (Turing.initList machine (BitstringEncoding.bitEncode xs)) =
    some (Turing.haltList machine (BitstringEncoding.bitEncode xs.tail)) := by
  let tail := BitstringEncoding.bitEncode xs.tail
  have hdrop : machine.step (Turing.initList machine (BitstringEncoding.bitEncode xs)) =
      some (cfg .copy none tail [] []) := by
    cases xs with
    | nil =>
      have he : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
      simpa [tail,he] using drop_nil
    | cons b bs => simpa [tail,encoded_cons] using drop_cell b (BitstringEncoding.bitEncode bs)
  have hc := copy_run tail [] [] none
  have hr := restore_run tail.reverse [] none
  have ht : 2*tail.length+3 = 1+((tail.length+1)+(tail.reverse.length+1)) := by simp; omega
  change runSteps machine.step (2*tail.length+3) (Turing.initList machine (BitstringEncoding.bitEncode xs)) = _
  rw [ht,runSteps_add]
  change (machine.step (Turing.initList machine (BitstringEncoding.bitEncode xs))).bind _ = _
  rw [hdrop]
  simp only [Option.bind_some]
  rw [runSteps_add,hc]
  simp only [Option.bind_some, List.append_nil]
  simpa [List.reverse_reverse] using hr

noncomputable def tailMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool) List.tail where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun xs := by
    refine ⟨⟨2*(BitstringEncoding.bitEncode xs.tail).length+3,?_⟩,?_⟩
    · have h := run_tail xs
      rw [runSteps_iterate] at h
      change (fun o => o.bind machine.step)^[2*(BitstringEncoding.bitEncode xs.tail).length+3]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode xs).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode xs.tail).map id))
      simpa using h
    · have hl : (BitstringEncoding.bitEncode xs.tail).length ≤ (BitstringEncoding.bitEncode xs).length := by
        cases xs with
        | nil => simp
        | cons b bs => simp [encoded_cons]; omega
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      omega

theorem tail_isPolyTime : ComplexityTheory.IsPolyTime (List.tail : List Bool → List Bool) := ⟨tailMachine⟩

end Shared.Beeping.NPcoNP.Source284BitListAccessTM2
