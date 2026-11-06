import Shared.ComplexityBridge.TM2Undelimit

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2FlattenBlocks
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
inductive Stack where | input | scratch | output
  deriving DecidableEq
inductive Label where | header | data | restore | done | reject
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.header,.data,.restore,.done,.reject] (by intro l; cases l <;> simp)
abbrev State := Option Bool × Bool

/-- The scratch stack holds the reverse of the already emitted flattened
payload. The flag says whether a block is open. -/
def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .header => .pop .input (fun s h => (h,s.2))
      (.branch (fun s => s.1.isSome)
        (.branch (fun s => s.1 == some true)
          (.load (fun s => (s.1,true)) (.goto (fun _ => .data)))
          (.load (fun s => (s.1,false)) (.goto (fun _ => .header))))
        (.branch Prod.snd (.goto (fun _ => .reject)) (.goto (fun _ => .restore))))
  | .data => .pop .input (fun s h => (h,s.2))
      (.branch (fun s => s.1.isSome)
        (.push .scratch (fun s => s.1.getD false) (.goto (fun _ => .header)))
        (.goto (fun _ => .reject)))
  | .restore => .pop .scratch (fun s h => (h,s.2))
      (.branch (fun s => s.1.isSome)
        (.push .output (fun s => s.1.getD false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)
  | .reject => .goto (fun _ => .reject)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .header
  σ := State
  initialState := (none,false)
  m := program

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

def cfg (l : Label) (v : Option Bool) (openBlock : Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,(v,openBlock),stackVals input scratch output⟩

def bitChunk (b : Bool) : List Bool := [b]

theorem block_code_cons (b : Bool) (bits : List Bool) : b::bits = bitChunk b ++ bits := by rfl

theorem block_code_nil : ([] : List Bool) = [] := rfl

theorem header_true (v : Option Bool) (flag : Bool) (input scratch output : List Bool) :
    machine.step (cfg .header v flag (true::input) scratch output) = some (cfg .data (some true) true input scratch output) := by
  change some (Cfg.mk (some Label.data) (some true,true)
    (Function.update (stackVals (true::input) scratch output) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_false (v : Option Bool) (flag : Bool) (input scratch output : List Bool) :
    machine.step (cfg .header v flag (false::input) scratch output) = some (cfg .header (some false) false input scratch output) := by
  change some (Cfg.mk (some Label.header) (some false,false)
    (Function.update (stackVals (false::input) scratch output) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_nil_closed (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .header v false [] scratch output) = some (cfg .restore none false [] scratch output) := by
  change some (Cfg.mk (some Label.restore) (none,false) (Function.update (stackVals [] scratch output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_nil_open (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .header v true [] scratch output) = some (cfg .reject none true [] scratch output) := by
  change some (Cfg.mk (some Label.reject) (none,true) (Function.update (stackVals [] scratch output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem data_cons (v : Option Bool) (flag : Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .data v flag (b::input) scratch output) =
      some (cfg .header (some b) flag input ((bitChunk b).reverse++scratch) output) := by
  change some (Cfg.mk (some Label.header) (some b,flag) _) = _
  congr 1; congr 1; funext k
  cases k <;> simp [stackVals,Function.update,bitChunk] <;> rfl

theorem data_nil (v : Option Bool) (flag : Bool) (scratch output : List Bool) :
    machine.step (cfg .data v flag [] scratch output) = some (cfg .reject none flag [] scratch output) := by
  change some (Cfg.mk (some Label.reject) (none,flag) (Function.update (stackVals [] scratch output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (flag : Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .restore v flag input (b::scratch) output) = some (cfg .restore (some b) flag input scratch (b::output)) := by
  change some (Cfg.mk (some Label.restore) (some b,flag)
    (Function.update (Function.update (stackVals input (b::scratch) output) .scratch scratch) .output (b::output))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (flag : Bool) (input output : List Bool) :
    machine.step (cfg .restore v flag input [] output) = some (cfg .done none flag input [] output) := by
  change some (Cfg.mk (some Label.done) (none,flag) (Function.update (stackVals input [] output) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .header none false input [] [] := by
  change Cfg.mk (some Label.header) (none,false) _ = Cfg.mk (some Label.header) (none,false) (stackVals input [] [])
  congr 1; funext k; cases k <;> simp [machine,stackVals] <;> rfl

/-- Scan one complete block. Its payload is accumulated in reverse without touching the following source blocks. -/
theorem block_run (bits tail scratch output : List Bool) (v : Option Bool) (flag : Bool) :
    runSteps machine.step (2*bits.length+1)
      (cfg .header v flag (BitstringEncoding.delimit bits ++ tail) scratch output) =
      some (cfg .header (some false) false tail
        ((bits).reverse ++ scratch) output) := by
  induction bits generalizing scratch v flag with
  | nil =>
    change machine.step (cfg .header v flag (false::tail) scratch output) = _
    simpa [block_code_nil] using header_false v flag tail scratch output
  | cons b bits ih =>
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(bits.length+1)+1 = ((2*bits.length+1)+1)+1 := by omega
    rw [hn,runSteps_front,header_true]
    change runSteps machine.step ((2*bits.length+1)+1)
      (cfg .data (some true) true (b::(BitstringEncoding.delimit bits ++ tail)) scratch output) = _
    rw [runSteps_front,data_cons]
    simpa [block_code_cons,List.reverse_append,List.append_assoc] using ih ((bitChunk b).reverse++scratch) (some b) true

theorem blocks_code_cons (bits : List Bool) (rest : List (List Bool)) :
    (bits::rest).flatten = bits ++ rest.flatten := rfl

def framed (blocks : List (List Bool)) : List Bool := (blocks.map BitstringEncoding.delimit).flatten

theorem blocks_run (blocks : List (List Bool)) (scratch output : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (framed blocks).length (cfg .header v false (framed blocks) scratch output) =
      some (cfg .header v' false [] ((blocks.flatten).reverse ++ scratch) output) := by
  induction blocks generalizing scratch v with
  | nil => exact ⟨v,by rfl⟩
  | cons bits blocks ih =>
    obtain ⟨v',h⟩ := ih ((bits).reverse++scratch) (some false)
    refine ⟨v',?_⟩
    have hb := block_run bits (framed blocks) scratch output v false
    change runSteps machine.step ((BitstringEncoding.delimit bits ++ framed blocks).length)
      (cfg .header v false (BitstringEncoding.delimit bits ++ framed blocks) scratch output) = _
    rw [List.length_append,BitstringEncoding.length_delimit,runSteps_add,hb]
    simpa [blocks_code_cons,List.reverse_append,List.append_assoc] using h

theorem restore_run (scratch input output : List Bool) (v : Option Bool) (flag : Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore v flag input scratch output) =
      some (cfg .restore v' flag input [] (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b scratch ih =>
    obtain ⟨v',h⟩ := ih (b::output) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

/-- Valid block sequences are parsed from the actual input, with the decoded payloads concatenated in their original order. -/
theorem valid_run (blocks : List (List Bool)) :
    runSteps machine.step ((framed blocks).length+(blocks.flatten).length+2)
      (Turing.initList machine (framed blocks)) = some (cfg .done none false [] [] (blocks.flatten)) := by
  obtain ⟨v,hs⟩ := blocks_run blocks [] [] none
  simp only [List.append_nil] at hs
  obtain ⟨u,hr⟩ := restore_run (blocks.flatten).reverse [] [] none false
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hr
  have hn : (framed blocks).length+(blocks.flatten).length+2 =
    (framed blocks).length+(((blocks.flatten).length+1)+1) := by omega
  rw [hn,initial_eq,runSteps_add,hs]
  change runSteps machine.step (((blocks.flatten).length+1)+1)
    (cfg .header v false [] (blocks.flatten).reverse []) = _
  rw [runSteps_front,header_nil_closed]
  change runSteps machine.step ((blocks.flatten).length+1)
    (cfg .restore none false [] (blocks.flatten).reverse []) = _
  rw [runSteps_add,hr]
  exact restore_nil u false [] (blocks.flatten)

/-- The flattened payload is no longer than the input. -/
theorem encoded_length_bound (blocks : List (List Bool)) :
    blocks.flatten.length ≤ (framed blocks).length := by
  induction blocks with
  | nil => rfl
  | cons bits blocks ih =>
    change (bits ++ blocks.flatten).length ≤ (BitstringEncoding.delimit bits ++ framed blocks).length
    rw [List.length_append,List.length_append,BitstringEncoding.length_delimit]
    omega

/-- An incomplete open block reaches reject after consuming its input. The
precondition excludes an empty input at a block boundary, which is valid. -/
theorem badBlock_run (input scratch output : List Bool) (v : Option Bool) (flag : Bool)
    (h : BitstringEncoding.undelimit input = none) (hopen : input ≠ [] ∨ flag = true) :
    ∃ t ≤ input.length+1, ∃ scratch',
      runSteps machine.step t (cfg .header v flag input scratch output) =
        some (cfg .reject none true [] scratch' output) := by
  induction input using List.twoStepInduction generalizing scratch v flag with
  | nil =>
    have hf : flag = true := by simpa using hopen
    subst flag
    exact ⟨1,by simp,scratch,header_nil_open v scratch output⟩
  | singleton b =>
    cases b with
    | false => simp [BitstringEncoding.undelimit] at h
    | true =>
      refine ⟨2,by simp,scratch,?_⟩
      rw [show 2 = 1+1 by decide,runSteps_front,header_true]
      exact data_nil (some true) true scratch output
  | cons_cons b c input ih =>
    cases b with
    | false => simp [BitstringEncoding.undelimit] at h
    | true =>
      have htail : BitstringEncoding.undelimit input = none := by
        cases hu : BitstringEncoding.undelimit input <;> simp [BitstringEncoding.undelimit,hu] at h ⊢
      obtain ⟨t,ht,scratch',hr⟩ := ih ((bitChunk c).reverse++scratch) (some c) true htail (Or.inr rfl)
      refine ⟨t+2,by simp only [List.length_cons]; omega,scratch',?_⟩
      rw [show t+2 = (t+1)+1 by omega,runSteps_front,header_true]
      change runSteps machine.step (t+1) (cfg .data (some true) true (c::input) scratch output) = _
      rw [runSteps_front,data_cons]
      exact hr

/-- Any malformed sequence reaches reject in linear time, including after
arbitrarily many valid preceding blocks. -/
theorem invalid_blocks_run (input scratch output : List Bool) (v : Option Bool)
    (h : BitstringEncoding.undelimitBlocks input = none) :
    ∃ t ≤ input.length+1, ∃ scratch',
      runSteps machine.step t (cfg .header v false input scratch output) =
        some (cfg .reject none true [] scratch' output) := by
  cases input with
  | nil => simp [BitstringEncoding.undelimitBlocks,BitstringEncoding.undelimitBlocksAux] at h
  | cons b bs =>
    cases hu : BitstringEncoding.undelimit (b::bs) with
    | none => exact badBlock_run (b::bs) scratch output v false hu (Or.inl (by simp))
    | some p =>
      rcases p with ⟨payload,tail⟩
      have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound (b::bs) payload tail hu
      have htail : BitstringEncoding.undelimitBlocks tail = none := by
        cases ht : BitstringEncoding.undelimitBlocks tail with
        | none => rfl
        | some blocks =>
          have hblocks := Shared.ComplexityBridge.CNFWitness.blocks_sound tail blocks ht
          have hfull : framed (payload::blocks) = b::bs := by
            simp only [framed,List.map_cons,List.flatten_cons,hblocks]
            exact he
          have hvalid := BitstringEncoding.undelimitBlocks_flatten_delimit (payload::blocks)
          change BitstringEncoding.undelimitBlocks (framed (payload::blocks)) = _ at hvalid
          rw [hfull] at hvalid
          rw [hvalid] at h
          contradiction
      have hlt : tail.length < (b::bs).length := by
        have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit,List.length_cons] at hl
        simp only [List.length_cons]
        omega
      obtain ⟨t,ht,scratch',hr⟩ := invalid_blocks_run tail
        ((payload).reverse++scratch) output (some false) htail
      have hb := block_run payload tail scratch output v false
      refine ⟨(2*payload.length+1)+t,?_,scratch',?_⟩
      · have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit,List.length_cons] at hl
        simp only [List.length_cons]
        omega
      · rw [← he,runSteps_add,hb]
        exact hr
termination_by input.length

/-- On every input the list-block parser reaches the decoder's correct branch.
The successful output concatenates all decoded block payloads. -/
theorem parse_progress (input : List Bool) :
    (∃ blocks, BitstringEncoding.undelimitBlocks input = some blocks ∧
      ∃ t ≤ 2*input.length+2, runSteps machine.step t (Turing.initList machine input) =
        some (cfg .done none false [] [] (blocks.flatten))) ∨
    (BitstringEncoding.undelimitBlocks input = none ∧ ∃ t ≤ input.length+1, ∃ scratch,
      runSteps machine.step t (Turing.initList machine input) = some (cfg .reject none true [] scratch [])) := by
  cases h : BitstringEncoding.undelimitBlocks input with
  | none =>
    right
    obtain ⟨t,ht,scratch,hr⟩ := invalid_blocks_run input [] [] none h
    exact ⟨rfl,t,ht,scratch,by simpa [initial_eq] using hr⟩
  | some blocks =>
    left
    have he := Shared.ComplexityBridge.CNFWitness.blocks_sound input blocks h
    change framed blocks = input at he
    refine ⟨blocks,rfl,(framed blocks).length+(blocks.flatten).length+2,?_,?_⟩
    · have hl := encoded_length_bound blocks
      rw [he] at hl ⊢
      omega
    · rw [← he]
      exact valid_run blocks

namespace Fixtures
/-- Empty input is the valid encoding of the empty block list. -/
example : (runSteps machine.step 2 (Turing.initList machine [])).map
    (fun c => (match c.l with | some .done => true | _ => false,c.stk .output)) = some (true,([] : List Bool)) := by
  change (Option.map (fun c => (match c.l with | some .done => true | _ => false,c.stk .output))
    (runSteps machine.step 2 (Turing.initList machine [])) : Option (Bool × List Bool)) = _
  decide

/-- A malformed second block is rejected after one valid empty block. -/
example : (runSteps machine.step 3 (Turing.initList machine [false,true])).map
    (fun c => (match c.l with | some .reject => true | _ => false,c.stk .scratch)) = some (true,([] : List Bool)) := by
  change (Option.map (fun c => (match c.l with | some .reject => true | _ => false,c.stk .scratch))
    (runSteps machine.step 3 (Turing.initList machine [false,true])) : Option (Bool × List Bool)) = _
  decide

/-- The output concatenates two blocks, including an empty one, in the correct order. -/
example : (runSteps machine.step 10 (Turing.initList machine (framed [[],[true,false]]))).map
    (fun c => (match c.l with | some .done => true | _ => false,c.stk .output)) =
      some (true,([true,false] : List Bool)) := by
  change (Option.map (fun c => (match c.l with | some .done => true | _ => false,c.stk .output))
    (runSteps machine.step 10 (Turing.initList machine (framed [[],[true,false]]))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2FlattenBlocks
