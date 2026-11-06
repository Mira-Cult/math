import Shared.ComplexityBridge.CNFChoiceOutput

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Count delimited list elements in unary, without decoding element values.
Each input bit is inspected by one finite TM2 statement block. -/
namespace Shared.ComplexityBridge.TM2ListUnaryLength
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | input | output deriving DecidableEq
inductive Label where | header | data deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.output] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.header,.data] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .header => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true) (.goto (fun _ => .data))
          (.push .output (fun _ => false) (.push .output (fun _ => true)
            (.push .output (fun _ => true) (.goto (fun _ => .header))))))
        (.load (fun _ => none) .halt))
  | .data => .pop .input (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .header)) (.load (fun _ => none) .halt))

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

def stackVals (input output : List Bool) : Stack → List Bool
  | .input => input | .output => output

def cfg (l : Label) (v : Option Bool) (input output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input output⟩

theorem header_true (v : Option Bool) (input output : List Bool) :
    machine.step (cfg .header v (true::input) output) = some (cfg .data (some true) input output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_false (v : Option Bool) (input output : List Bool) :
    machine.step (cfg .header v (false::input) output) = some (cfg .header (some false) input (true::true::false::output)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem data_cons (v : Option Bool) (b : Bool) (input output : List Bool) :
    machine.step (cfg .data v (b::input) output) = some (cfg .header (some b) input output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_nil (v : Option Bool) (output : List Bool) :
    machine.step (cfg .header v [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine]

theorem block_run (bits tail output : List Bool) (v : Option Bool) :
    runSteps machine.step (2*bits.length+1) (cfg .header v (BitstringEncoding.delimit bits++tail) output) =
      some (cfg .header (some false) tail (true::true::false::output)) := by
  induction bits generalizing v with
  | nil => simpa [BitstringEncoding.delimit,runSteps] using header_false v tail output
  | cons b bits ih =>
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(bits.length+1)+1 = (2*bits.length+1+1)+1 := by omega
    rw [hn,runSteps_front,header_true]
    change runSteps machine.step (2*bits.length+1+1) (cfg .data (some true) (b::(BitstringEncoding.delimit bits++tail)) output) = _
    rw [runSteps_front,data_cons]
    exact ih (some b)

def framed (blocks : List (List Bool)) : List Bool := (blocks.map BitstringEncoding.delimit).flatten

theorem encoded_tokens_commute (n : Nat) :
    BitstringEncoding.bitEncode (List.replicate n true) ++ [true,true,false] =
      [true,true,false] ++ BitstringEncoding.bitEncode (List.replicate n true) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ,Shared.ComplexityBridge.TM2ListCodec.Decode.bitEncode_cons,List.append_assoc,ih]

theorem blocks_run (blocks : List (List Bool)) (output : List Bool) (v : Option Bool) :
    runSteps machine.step ((framed blocks).length+1) (cfg .header v (framed blocks) output) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode (List.replicate blocks.length true)++output)) := by
  induction blocks generalizing output v with
  | nil =>
    have he : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
    simpa [framed,runSteps,he] using header_nil v output
  | cons b blocks ih =>
    have hf : framed (b::blocks) = BitstringEncoding.delimit b ++ framed blocks := rfl
    have hl : (framed (b::blocks)).length+1 = (2*b.length+1)+((framed blocks).length+1) := by
      rw [hf,List.length_append,BitstringEncoding.length_delimit]; omega
    rw [hl,hf,runSteps_add,block_run]
    have h := ih (true::true::false::output) (some false)
    have hc : BitstringEncoding.bitEncode (List.replicate blocks.length true) ++ (true::true::false::output) =
        (true::true::false::BitstringEncoding.bitEncode (List.replicate blocks.length true)) ++ output := by
      simpa [List.append_assoc] using congrArg (fun xs => xs++output) (encoded_tokens_commute blocks.length)
    simpa [Shared.ComplexityBridge.TM2ListCodec.Decode.bitEncode_cons,framed,List.replicate_succ,hc] using h

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .header none input [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals]

def unaryLength {α : Type} (xs : List α) : List Bool := List.replicate xs.length true

theorem run_list {α : Type} [BitstringEncoding α] (xs : List α) :
    runSteps machine.step ((BitstringEncoding.bitEncode xs).length+1)
      (Turing.initList machine (BitstringEncoding.bitEncode xs)) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode (unaryLength xs))) := by
  have h := blocks_run (xs.map BitstringEncoding.bitEncode) [] none
  have he : framed (xs.map BitstringEncoding.bitEncode) = BitstringEncoding.bitEncode xs := rfl
  simpa [he,initial_eq,unaryLength] using h

noncomputable def timeMachine {α : Type} [BitstringEncoding α] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : List α → List Bool)
      (BitstringEncoding.bitEncode : List Bool → List Bool) (unaryLength (α := α)) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + Polynomial.C 1
  outputsFun xs := by
    refine ⟨⟨(BitstringEncoding.bitEncode xs).length+1,?_⟩,?_⟩
    · have h := run_list xs
      rw [runSteps_iterate] at h
      change (fun o => o.bind machine.step)^[(BitstringEncoding.bitEncode xs).length+1]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode xs).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (unaryLength xs)).map id))
      simpa using h
    · simp

theorem unaryLength_isPolyTime {α : Type} [BitstringEncoding α] :
    ComplexityTheory.IsPolyTime (unaryLength (α := α)) := ⟨timeMachine⟩

/-- This is the actual choice clause at the head of `disjoin`: the count is
obtained from the encoded input list, not from a binary-coded number. -/
theorem disjoin_choices_isPolyTime : ComplexityTheory.IsPolyTime
    (fun fs : List Shared.ComplexityBridge.CNF.Formula =>
      Shared.ComplexityBridge.CNFDisjunction.choices 0 fs.length) := by
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    (unaryLength (α := Shared.ComplexityBridge.CNF.Formula))
    Shared.ComplexityBridge.CNFChoiceOutput.choiceClause unaryLength_isPolyTime
    Shared.ComplexityBridge.CNFChoiceOutput.choiceClause_isPolyTime
  simpa [unaryLength,Shared.ComplexityBridge.CNFChoiceOutput.choiceClause] using h

namespace Fixtures
example : unaryLength ([[],[[]]] : List Shared.ComplexityBridge.CNF.Formula) = [true,true] := rfl
example : runSteps machine.step ((BitstringEncoding.bitEncode ([[],[[]]] : List Shared.ComplexityBridge.CNF.Formula)).length+1)
    (Turing.initList machine (BitstringEncoding.bitEncode ([[],[[]]] : List Shared.ComplexityBridge.CNF.Formula))) =
    some (Turing.haltList machine (BitstringEncoding.bitEncode [true,true])) := by
  simpa [unaryLength] using run_list ([[],[[]]] : List Shared.ComplexityBridge.CNF.Formula)
end Fixtures
end Shared.ComplexityBridge.TM2ListUnaryLength
