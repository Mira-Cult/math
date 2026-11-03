import Shared.ComplexityBridge.CNFLiteralConstructor
import Shared.ComplexityBridge.TM2ListAppend

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Reverse a canonically encoded list in a finite TM2. The input is a
sequence of delimited element encodings; each entire block is prepended to
the output without reversing the bits inside it. -/
namespace Shared.ComplexityBridge.TM2ListReverse
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNFLiteralConstructor (framedBits delimit_prefix)

inductive Stack where | input | scratch | output deriving DecidableEq
inductive Label where | header | data | restore deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.header,.data,.restore] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .header => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true) (.goto (fun _ => .data))
          (.push .output (fun _ => false) (.goto (fun _ => .restore))))
        (.load (fun _ => none) .halt))
  | .data => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false) (.goto (fun _ => .header)))
        (.load (fun _ => none) .halt))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun v => v.getD false)
          (.push .output (fun _ => true) (.goto (fun _ => .restore))))
        (.goto (fun _ => .header)))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .header
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem header_true (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .header v (true::input) scratch output) = some (cfg .data (some true) input scratch output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_false (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .header v (false::input) scratch output) = some (cfg .restore (some false) input scratch (false::output)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_nil (v : Option Bool) (output : List Bool) :
    machine.step (cfg .header v [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine]

theorem data_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .data v (b::input) scratch output) = some (cfg .header (some b) input (b::scratch) output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .restore v input (b::scratch) output) =
      some (cfg .restore (some b) input scratch (true::b::output)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (input output : List Bool) :
    machine.step (cfg .restore v input [] output) = some (cfg .header none input [] output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_run (bits tail scratch output : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (2*bits.length)
      (cfg .header v (BitstringEncoding.delimit bits ++ tail) scratch output) =
      some (cfg .header v' (false::tail) (bits.reverse++scratch) output) := by
  induction bits generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit]⟩
  | cons b bits ih =>
    obtain ⟨v',hr⟩ := ih (b::scratch) (some b)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(bits.length+1) = (2*bits.length+1)+1 := by omega
    rw [hn,runSteps_front,header_true]
    change runSteps machine.step (2*bits.length+1)
      (cfg .data (some true) (b::(BitstringEncoding.delimit bits++tail)) scratch output) = _
    rw [runSteps_front,data_cons]
    simpa [List.reverse_cons,List.append_assoc] using hr

theorem restore_run (scratch input output : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore v input scratch output) =
      some (cfg .restore v' input [] (framedBits scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact ⟨v,by simp [runSteps,framedBits]⟩
  | cons b scratch ih =>
    obtain ⟨v',hr⟩ := ih (true::b::output) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [framedBits,List.reverse_cons,List.flatMap_append,List.append_assoc] using hr

theorem block_run (bits tail output : List Bool) (v : Option Bool) :
    runSteps machine.step (3*bits.length+2)
      (cfg .header v (BitstringEncoding.delimit bits++tail) [] output) =
      some (cfg .header none tail [] (BitstringEncoding.delimit bits++output)) := by
  obtain ⟨w,hs⟩ := scan_run bits tail [] output v
  simp only [List.append_nil] at hs
  obtain ⟨z,hr⟩ := restore_run bits.reverse tail (false::output) (some false)
  simp only [List.reverse_reverse,List.length_reverse] at hr
  have hn : 3*bits.length+2 = (2*bits.length+1)+(bits.length+1) := by omega
  rw [hn,runSteps_add,runSteps_add,hs]
  change runSteps machine.step 1 (cfg .header w (false::tail) bits.reverse output) >>= _ = _
  rw [show runSteps machine.step 1 (cfg .header w (false::tail) bits.reverse output) =
    machine.step (cfg .header w (false::tail) bits.reverse output) by rfl,header_false]
  change runSteps machine.step (bits.length+1) (cfg .restore (some false) tail bits.reverse (false::output)) = _
  rw [runSteps_add,hr]
  simpa [runSteps,delimit_prefix,List.append_assoc] using restore_nil z tail (framedBits bits++false::output)

def framed (blocks : List (List Bool)) : List Bool := (blocks.map BitstringEncoding.delimit).flatten

theorem blocks_run (blocks : List (List Bool)) (output : List Bool) (v : Option Bool) :
    ∃ t ≤ 3*(framed blocks).length+1,
      runSteps machine.step t (cfg .header v (framed blocks) [] output) =
        some (Turing.haltList machine (framed blocks.reverse++output)) := by
  induction blocks generalizing output v with
  | nil =>
    refine ⟨1,by simp [framed],?_⟩
    simpa [runSteps,framed] using header_nil v output
  | cons b blocks ih =>
    obtain ⟨t,ht,hr⟩ := ih (BitstringEncoding.delimit b++output) none
    have hlen : (framed (b::blocks)).length = 2*b.length+1+(framed blocks).length := by
      simp [framed,BitstringEncoding.length_delimit]
    refine ⟨(3*b.length+2)+t,?_,?_⟩
    · rw [hlen]; omega
    · rw [show framed (b::blocks) = BitstringEncoding.delimit b++framed blocks by rfl,runSteps_add,block_run]
      simpa [framed,List.reverse_cons,List.map_append,List.flatten_append,List.append_assoc] using hr

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .header none input [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals]

theorem encoded_reverse {α : Type} [BitstringEncoding α] (xs : List α) :
    BitstringEncoding.bitEncode xs.reverse = framed ((xs.map BitstringEncoding.bitEncode).reverse) := by
  change (((xs.reverse.map BitstringEncoding.bitEncode).map BitstringEncoding.delimit).flatten) = _
  simp [framed,List.map_reverse]

theorem encoded_eq {α : Type} [BitstringEncoding α] (xs : List α) :
    BitstringEncoding.bitEncode xs = framed (xs.map BitstringEncoding.bitEncode) := rfl

/-- Reverse the input list, with linear time in its full serialized size. -/
theorem run_list {α : Type} [BitstringEncoding α] (xs : List α) :
    ∃ t ≤ 3*(BitstringEncoding.bitEncode xs).length+1,
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.bitEncode xs)) =
        some (Turing.haltList machine (BitstringEncoding.bitEncode xs.reverse)) := by
  obtain ⟨t,ht,hr⟩ := blocks_run (xs.map BitstringEncoding.bitEncode) [] none
  refine ⟨t,?_,?_⟩
  · simpa [encoded_eq] using ht
  · simpa [initial_eq,encoded_eq,encoded_reverse] using hr

noncomputable def timeMachine {α : Type} [BitstringEncoding α] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : List α → List Bool)
      (BitstringEncoding.bitEncode : List α → List Bool) List.reverse where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 1
  outputsFun xs := by
    classical
    let t := Nat.find (run_list xs)
    have ht := (Nat.find_spec (run_list xs)).1
    have hr := (Nat.find_spec (run_list xs)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode xs).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode xs.reverse).map id))
      simpa using hr
    · simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using ht

theorem reverse_isPolyTime {α : Type} [BitstringEncoding α] :
    ComplexityTheory.IsPolyTime (List.reverse : List α → List α) := ⟨timeMachine⟩

theorem clause_reverse_isPolyTime :
    ComplexityTheory.IsPolyTime (List.reverse : Shared.ComplexityBridge.CNF.Clause → Shared.ComplexityBridge.CNF.Clause) :=
  reverse_isPolyTime

theorem formula_reverse_isPolyTime :
    ComplexityTheory.IsPolyTime (List.reverse : Shared.ComplexityBridge.CNF.Formula → Shared.ComplexityBridge.CNF.Formula) :=
  reverse_isPolyTime

namespace Fixtures
example : ∃ t ≤ 3*(BitstringEncoding.bitEncode ([[],[true,false],[false]] : List (List Bool))).length+1,
    runSteps machine.step t (Turing.initList machine (BitstringEncoding.bitEncode ([[],[true,false],[false]] : List (List Bool)))) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode ([[false],[true,false],[]] : List (List Bool)))) := by
  simpa using run_list ([[],[true,false],[false]] : List (List Bool))
end Fixtures

end Shared.ComplexityBridge.TM2ListReverse
