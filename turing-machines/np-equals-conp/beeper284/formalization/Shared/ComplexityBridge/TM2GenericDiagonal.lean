import Shared.ComplexityBridge.TM2TypedPairMap
import Shared.ComplexityBridge.TM2PairSwap
import Shared.ComplexityBridge.TM2ListCodec

/-! Adapted from the shared `TM2Diagonal` machine: this variant copies raw
canonical bytes and therefore applies to any encoded type. -/
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2GenericDiagonal
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2ListCodec (Stack stackVals)
inductive Label where | scan1 | restore1 | scan2 | restore2 deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.scan1,.restore1,.scan2,.restore2] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .scan1 => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan1))) (.goto (fun _ => .restore1)))
  | .restore1 => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .input (fun v => v.getD false)
          (.push .output (fun v => v.getD false) (.goto (fun _ => .restore1))))
        (.goto (fun _ => .scan2)))
  | .scan2 => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan2)))
        (.push .output (fun _ => false) (.goto (fun _ => .restore2))))
  | .restore2 => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun v => v.getD false)
          (.push .output (fun _ => true) (.goto (fun _ => .restore2))))
        (.load (fun _ => none) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .scan1
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem scan1_cons (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .scan1 v (b::xs) scratch out) = some (cfg .scan1 (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem scan1_nil (v : Option Bool) (scratch out : List Bool) :
    machine.step (cfg .scan1 v [] scratch out) = some (cfg .restore1 none [] scratch out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem restore1_cons (v : Option Bool) (b : Bool) (input scratch out : List Bool) :
    machine.step (cfg .restore1 v input (b::scratch) out) =
      some (cfg .restore1 (some b) (b::input) scratch (b::out)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem restore1_nil (v : Option Bool) (input out : List Bool) :
    machine.step (cfg .restore1 v input [] out) = some (cfg .scan2 none input [] out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem scan2_cons (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .scan2 v (b::xs) scratch out) = some (cfg .scan2 (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem scan2_nil (v : Option Bool) (scratch out : List Bool) :
    machine.step (cfg .scan2 v [] scratch out) = some (cfg .restore2 none [] scratch (false::out)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem restore2_cons (v : Option Bool) (b : Bool) (scratch out : List Bool) :
    machine.step (cfg .restore2 v [] (b::scratch) out) =
      some (cfg .restore2 (some b) [] scratch (true::b::out)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem restore2_nil (v : Option Bool) (out : List Bool) :
    machine.step (cfg .restore2 v [] [] out) = some (Turing.haltList machine out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine] <;> rfl

def encoded (xs : List Bool) : List Bool := xs
def prefixBits (xs : List Bool) : List Bool := xs.flatMap (fun b => [true,b])
theorem prefix_eq (xs : List Bool) : BitstringEncoding.delimit xs = prefixBits xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [BitstringEncoding.delimit,prefixBits,ih]

theorem scan1_loop (xs scratch out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step xs.length (cfg .scan1 v xs scratch out) =
      some (cfg .scan1 v' [] (xs.reverse++scratch) out) := by
  induction xs generalizing v scratch with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b xs ih =>
    obtain ⟨z,h⟩ := ih (b::scratch) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,scan1_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore1_loop (scratch input out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore1 v input scratch out) =
      some (cfg .restore1 v' (scratch.reverse++input) [] (encoded scratch.reverse++out)) := by
  induction scratch generalizing input out v with
  | nil => exact ⟨v,by simp [runSteps,encoded]⟩
  | cons b scratch ih =>
    obtain ⟨z,h⟩ := ih (b::input) (b::out) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,restore1_cons]
    simpa [encoded,List.reverse_cons,List.flatMap_append,List.append_assoc] using h

theorem scan2_loop (xs scratch out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step xs.length (cfg .scan2 v xs scratch out) =
      some (cfg .scan2 v' [] (xs.reverse++scratch) out) := by
  induction xs generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b xs ih =>
    obtain ⟨z,h⟩ := ih (b::scratch) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,scan2_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore2_loop (scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore2 v [] scratch out) =
      some (Turing.haltList machine (prefixBits scratch.reverse++out)) := by
  induction scratch generalizing out v with
  | nil =>
    change machine.step (cfg .restore2 v [] [] out) = _
    simpa [prefixBits] using restore2_nil v out
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore2_cons]
    simpa [prefixBits,List.reverse_cons,List.flatMap_append,List.append_assoc] using ih (true::b::out) (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .scan1 none input [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals,Turing.initList] <;> rfl

/-- From raw bytes, produce `delimit xs ++ xs` and halt with every
non-output stack empty. Both copies and all boundary tests cost steps. -/
theorem run (xs : List Bool) :
    runSteps machine.step (4*xs.length+4) (Turing.initList machine xs) =
      some (Turing.haltList machine (BitstringEncoding.delimit xs ++ xs)) := by
  obtain ⟨a,ha⟩ := scan1_loop xs [] [] none
  simp only [List.append_nil] at ha
  obtain ⟨b,hb⟩ := restore1_loop xs.reverse [] [] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hb
  obtain ⟨c,hc⟩ := scan2_loop xs [] (encoded xs) none
  simp only [List.append_nil] at hc
  have hd := restore2_loop xs.reverse (false::encoded xs) none
  simp only [List.reverse_reverse,List.length_reverse] at hd
  have hout : prefixBits xs ++ false::encoded xs = BitstringEncoding.delimit xs ++ xs := by
    rw [prefix_eq]
    simp [encoded,List.append_assoc]
  rw [hout] at hd
  have hcost : 4*xs.length+4 = xs.length+(1+(xs.length+(1+(xs.length+(1+(xs.length+1)))))) := by omega
  rw [initial_eq,hcost,runSteps_add,ha]
  change runSteps machine.step (1+(xs.length+(1+(xs.length+(1+(xs.length+1)))))) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .scan1 a [] xs.reverse [])).bind _ = _
  rw [scan1_nil]
  change runSteps machine.step (xs.length+(1+(xs.length+(1+(xs.length+1))))) _ = _
  rw [runSteps_add,hb]
  change runSteps machine.step (1+(xs.length+(1+(xs.length+1)))) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .restore1 b xs [] (encoded xs))).bind _ = _
  rw [restore1_nil]
  change runSteps machine.step (xs.length+(1+(xs.length+1))) _ = _
  rw [runSteps_add,hc]
  change runSteps machine.step (1+(xs.length+1)) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .scan2 c [] xs.reverse (encoded xs))).bind _ = _
  rw [scan2_nil]
  exact hd

/-- A canonical encoding can be duplicated without decoding its value. -/
noncomputable def timeMachine {α : Type} [BitstringEncoding α] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : α → List Bool)
      (BitstringEncoding.bitEncode : α × α → List Bool) (fun x : α => (x,x)) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 4*Polynomial.X+Polynomial.C 4
  outputsFun x := by
    let xs := BitstringEncoding.bitEncode x
    refine ⟨⟨4*xs.length+4,?_⟩,?_⟩
    · have hr := run xs
      rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[4*xs.length+4]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode x).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (x,x)).map id))
      have he : BitstringEncoding.bitEncode (x,x) = BitstringEncoding.delimit xs ++ xs := rfl
      rw [he]
      simpa [xs] using hr
    · simp [xs]

theorem diagonal_isPolyTime {α : Type} [BitstringEncoding α] :
    ComplexityTheory.IsPolyTime (fun x : α => (x,x)) := ⟨timeMachine⟩

/-- A single polynomial-time computation returns its result together with
its original canonical input. No copy of the input is preloaded. -/
theorem withInput_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (F : α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (fun x : α => (F x,x)) := by
  let d : α → α × α := fun x => (x,x)
  let m : α × α → β × α := Shared.ComplexityBridge.TM2TypedPairMap.pairMap F
  have hd : ComplexityTheory.IsPolyTime d := diagonal_isPolyTime
  have hm : ComplexityTheory.IsPolyTime m := Shared.ComplexityBridge.TM2TypedPairMap.pairMap_isPolyTime F hF
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp d m hd hm
  simpa [d,m,Shared.ComplexityBridge.TM2TypedPairMap.pairMap] using h

/-- The actual guard-clause machine can return both its result and the exact
original `(index, clause)` input in one polynomial-time computation. -/
theorem guard_with_input_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × Shared.ComplexityBridge.CNF.Clause =>
      (Shared.ComplexityBridge.CNFDisjunction.guardClause p.1 p.2,p)) :=
  withInput_isPolyTime _ Shared.ComplexityBridge.TM2PairSwap.guardClause_isPolyTime

namespace Fixtures
example : runSteps machine.step 4 (Turing.initList machine []) = some (Turing.haltList machine [false]) := by
  simpa [BitstringEncoding.delimit] using run []
example : runSteps machine.step 12 (Turing.initList machine [true,false]) =
    some (Turing.haltList machine [true,true,true,false,false,true,false]) := by
  simpa [BitstringEncoding.delimit] using run [true,false]
end Fixtures
end Shared.ComplexityBridge.TM2GenericDiagonal
