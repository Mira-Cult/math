import Shared.ComplexityBridge.TM2GuardAllStep
import Shared.ComplexityBridge.TM2ContextMapSplit

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Install one completed fold-step output as the next serialized state.
All stacks are explicit. This transfer does not invoke the evaluator or
construct the enclosing repeated driver. -/
namespace Shared.ComplexityBridge.TM2FoldStateInstall
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Key := Shared.ComplexityBridge.TM2ContextMapSplit.Key
abbrev SourceLabel := Shared.ComplexityBridge.TM2ContextMapSplit.Label
inductive Phase where | clear | scan | restore | ready deriving DecidableEq
instance : Fintype Phase := Fintype.ofList [.clear,.scan,.restore,.ready] (by intro l; cases l <;> simp)
abbrev Label := SourceLabel ⊕ Phase

def program : Label → Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .inr .clear => .pop (.inl .context) (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .inr .clear)) (.goto (fun _ => .inr .scan)))
  | .inr .scan => .pop (.inl .core) (fun _ h => h)
      (.branch Option.isSome
        (.push (.inl .scratch) (fun v => v.getD false) (.goto (fun _ => .inr .scan)))
        (.goto (fun _ => .inr .restore)))
  | .inr .restore => .pop (.inl .scratch) (fun _ h => h)
      (.branch Option.isSome
        (.push (.inl .context) (fun v => v.getD false) (.goto (fun _ => .inr .restore)))
        (.load (fun _ => none) (.goto (fun _ => .inr .ready))))
  | .inr .ready => .goto (fun _ => .inr .ready)
  | .inl _ => .goto (fun _ => .inr .ready)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inl .core
  k₁ := .inl .context
  Γ := fun _ => Bool
  Λ := Label
  main := .inr .clear
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Phase) (v : Option Bool) (ctx scratch core acc tail : List Bool) : machine.Cfg :=
  ⟨some (.inr l),v,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals
    (Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals ctx [] scratch core acc) tail⟩

theorem clear_cons (v : Option Bool) (b : Bool) (ctx scratch core acc tail : List Bool) :
    machine.step (cfg .clear v (b::ctx) scratch core acc tail) =
      some (cfg .clear (some b) ctx scratch core acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem clear_nil (v : Option Bool) (scratch core acc tail : List Bool) :
    machine.step (cfg .clear v [] scratch core acc tail) = some (cfg .scan none [] scratch core acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem scan_cons (v : Option Bool) (b : Bool) (scratch core acc tail : List Bool) :
    machine.step (cfg .scan v [] scratch (b::core) acc tail) =
      some (cfg .scan (some b) [] (b::scratch) core acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem scan_nil (v : Option Bool) (scratch acc tail : List Bool) :
    machine.step (cfg .scan v [] scratch [] acc tail) = some (cfg .restore none [] scratch [] acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (ctx scratch acc tail : List Bool) :
    machine.step (cfg .restore v ctx (b::scratch) [] acc tail) =
      some (cfg .restore (some b) (b::ctx) scratch [] acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem restore_nil (v : Option Bool) (ctx acc tail : List Bool) :
    machine.step (cfg .restore v ctx [] [] acc tail) = some (cfg .ready none ctx [] [] acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem clear_run (ctx scratch core acc tail : List Bool) (v : Option Bool) :
    runSteps machine.step (ctx.length+1) (cfg .clear v ctx scratch core acc tail) =
      some (cfg .scan none [] scratch core acc tail) := by
  induction ctx generalizing v with
  | nil => exact clear_nil v scratch core acc tail
  | cons b ctx ih =>
    rw [List.length_cons,show ctx.length+1+1 = (ctx.length+1)+1 by omega,runSteps_front,clear_cons]
    exact ih (some b)

theorem scan_run (core scratch acc tail : List Bool) (v : Option Bool) :
    runSteps machine.step (core.length+1) (cfg .scan v [] scratch core acc tail) =
      some (cfg .restore none [] (core.reverse++scratch) [] acc tail) := by
  induction core generalizing scratch v with
  | nil => exact scan_nil v scratch acc tail
  | cons b core ih =>
    rw [List.length_cons,show core.length+1+1 = (core.length+1)+1 by omega,runSteps_front,scan_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restore_run (scratch ctx acc tail : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v ctx scratch [] acc tail) =
      some (cfg .ready none (scratch.reverse++ctx) [] [] acc tail) := by
  induction scratch generalizing ctx v with
  | nil => exact restore_nil v ctx acc tail
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::ctx) (some b)

/-- Install the entire returned bitstring in order, erase the old state, and
preserve the unread stream and unrelated accumulator. -/
theorem install_run (old result acc tail : List Bool) :
    runSteps machine.step (old.length+2*result.length+3)
      (cfg .clear none old [] result acc tail) = some (cfg .ready none result [] [] acc tail) := by
  have hc := clear_run old [] result acc tail none
  have hs := scan_run result [] acc tail none
  simp only [List.append_nil] at hs
  have hr := restore_run result.reverse [] acc tail none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  rw [show old.length+2*result.length+3 = (old.length+1)+((result.length+1)+(result.length+1)) by omega,
    runSteps_add,hc]
  change runSteps machine.step ((result.length+1)+(result.length+1)) _ = _
  rw [runSteps_add,hs]
  exact hr

/-- A typed state update uses the exact canonical encoding of the next state;
the number of TM2 blocks depends only on the two serialized state lengths. -/
theorem install_encoded {α : Type} [BitstringEncoding α] (old new : α) (acc tail : List Bool) :
    runSteps machine.step ((BitstringEncoding.bitEncode old).length+2*(BitstringEncoding.bitEncode new).length+3)
      (cfg .clear none (BitstringEncoding.bitEncode old) [] (BitstringEncoding.bitEncode new) acc tail) =
      some (cfg .ready none (BitstringEncoding.bitEncode new) [] [] acc tail) := install_run _ _ _ _

namespace Fixtures
example : runSteps machine.step 3 (cfg .clear none [] [] [] [] []) =
    some (cfg .ready none [] [] [] [] []) := by simpa using install_run [] [] [] []
example : runSteps machine.step 7 (cfg .clear none [true,false] [] [false] [true] [false,true]) =
    some (cfg .ready none [false] [] [] [true] [false,true]) := by
  simpa using install_run [true,false] [false] [true] [false,true]
end Fixtures
end Shared.ComplexityBridge.TM2FoldStateInstall
