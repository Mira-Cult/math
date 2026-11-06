import Shared.ComplexityBridge.CNFChoiceBitCosts

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! A finite TM2 emits one selector clause-element block on a reverse-oriented
accumulator while preserving the binary index. The entry and exit boundaries
are explicit stacks; the surrounding loop is a separate obligation. -/
namespace Shared.ComplexityBridge.CNFChoiceEmitter
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNFChoiceBitCosts (block)

inductive Stack where | index | scratch | accumulator deriving DecidableEq
inductive Label where | start | emit | restore | done deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.index,.scratch,.accumulator] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.start,.emit,.restore,.done] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .start => .push .accumulator (fun _ => true) (.push .accumulator (fun _ => true)
      (.push .accumulator (fun _ => true) (.push .accumulator (fun _ => true) (.goto (fun _ => .emit)))))
  | .emit => .pop .index (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false)
          (.push .accumulator (fun _ => true) (.push .accumulator (fun _ => true)
            (.push .accumulator (fun _ => true) (.push .accumulator (fun v => v.getD false)
              (.goto (fun _ => .emit)))))))
        (.push .accumulator (fun _ => true) (.push .accumulator (fun _ => false)
          (.push .accumulator (fun _ => true) (.push .accumulator (fun _ => true)
            (.push .accumulator (fun _ => false) (.goto (fun _ => .restore))))))))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .index (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .index
  k₁ := .accumulator
  Γ := fun _ => Bool
  Λ := Label
  main := .start
  σ := Option Bool
  initialState := none
  m := program

def stackVals (index scratch acc : List Bool) : Stack → List Bool
  | .index => index | .scratch => scratch | .accumulator => acc

def cfg (l : Label) (v : Option Bool) (index scratch acc : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals index scratch acc⟩

theorem start_step (v : Option Bool) (bits scratch acc : List Bool) :
    machine.step (cfg .start v bits scratch acc) =
      some (cfg .emit v bits scratch (true::true::true::true::acc)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem emit_cons (v : Option Bool) (b : Bool) (bits scratch acc : List Bool) :
    machine.step (cfg .emit v (b::bits) scratch acc) =
      some (cfg .emit (some b) bits (b::scratch) (b::true::true::true::acc)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem emit_nil (v : Option Bool) (scratch acc : List Bool) :
    machine.step (cfg .emit v [] scratch acc) =
      some (cfg .restore none [] scratch (false::true::true::false::true::acc)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (index scratch acc : List Bool) :
    machine.step (cfg .restore v index (b::scratch) acc) =
      some (cfg .restore (some b) (b::index) scratch acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (index acc : List Bool) :
    machine.step (cfg .restore v index [] acc) = some (cfg .done none index [] acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

def chunks (bits : List Bool) : List Bool := bits.flatMap (fun b => [true,true,true,b])

theorem nested_delimit (bits : List Bool) :
    BitstringEncoding.delimit (BitstringEncoding.delimit bits ++ [true]) =
      chunks bits ++ [true,false,true,true,false] := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [BitstringEncoding.delimit,chunks,ih]

theorem block_expand (bits : List Bool) :
    block bits = [true,true,true,true] ++ chunks bits ++ [true,false,true,true,false] := by
  change true::true::true::true::BitstringEncoding.delimit (BitstringEncoding.delimit bits ++ [true]) = _
  rw [nested_delimit]
  rfl

theorem emit_run (bits scratch acc : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step bits.length (cfg .emit v bits scratch acc) =
      some (cfg .emit v' [] (bits.reverse++scratch) ((chunks bits).reverse++acc)) := by
  induction bits generalizing scratch acc v with
  | nil => exact ⟨v,by simp [runSteps,chunks]⟩
  | cons b bits ih =>
    obtain ⟨v',hr⟩ := ih (b::scratch) (b::true::true::true::acc) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,emit_cons]
    simpa [chunks,List.reverse_cons,List.flatMap_append,List.append_assoc] using hr

theorem restore_run (scratch index acc : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v index scratch acc) =
      some (cfg .done none (scratch.reverse++index) [] acc) := by
  induction scratch generalizing index v with
  | nil => exact restore_nil v index acc
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::index) (some b)

/-- One positive finite machine segment emits exactly the block used by the
bit-level selector generator. The index is unchanged and scratch is empty. -/
theorem run (bits acc : List Bool) :
    runSteps machine.step (2*bits.length+3) (cfg .start none bits [] acc) =
      some (cfg .done none bits [] ((block bits).reverse++acc)) := by
  obtain ⟨v,he⟩ := emit_run bits [] (true::true::true::true::acc) none
  simp only [List.append_nil] at he
  have hr := restore_run bits.reverse []
    (false::true::true::false::true::((chunks bits).reverse++true::true::true::true::acc)) none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  have hn : 2*bits.length+3 = 1+(bits.length+(1+(bits.length+1))) := by omega
  rw [hn,runSteps_add]
  change (machine.step (cfg .start none bits [] acc)).bind _ = _
  rw [start_step]
  change runSteps machine.step (bits.length+(1+(bits.length+1))) _ = _
  rw [runSteps_add,he]
  change runSteps machine.step (1+(bits.length+1)) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .emit v [] bits.reverse ((chunks bits).reverse++true::true::true::true::acc))).bind _ = _
  rw [emit_nil]
  simpa [block_expand,List.reverse_append,List.append_assoc] using hr

/-- The machine boundary agrees with the accumulator component of the
executable generator step. Incrementing the preserved index is separate. -/
theorem run_generator_output (bits acc : List Bool) :
    runSteps machine.step (2*bits.length+3) (cfg .start none bits [] acc) =
      some (cfg .done none bits [] ((Shared.ComplexityBridge.CNFChoiceBitCosts.step bits acc).1.2)) := by
  rw [Shared.ComplexityBridge.CNFChoiceBitCosts.step_correct]
  exact run bits acc

namespace Fixtures
example : runSteps machine.step 3 (cfg .start none [] [] []) =
    some (cfg .done none [] [] [false,true,true,false,true,true,true,true,true]) := by
  simpa [block,BitstringEncoding.delimit] using run [] []
end Fixtures

end Shared.ComplexityBridge.CNFChoiceEmitter
