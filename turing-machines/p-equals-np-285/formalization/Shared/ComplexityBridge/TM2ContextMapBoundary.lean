import Shared.ComplexityBridge.TM2MapSizeBounds
import Shared.ComplexityBridge.CNFChoiceEmitter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Finite data-movement routines for a context-preserving map: construct
one canonical `(context, item)` input while retaining the context, then
frame a returned result onto a reverse-oriented accumulator. Both interfaces
use explicitly populated stacks; they do not invoke the item machine. -/
namespace Shared.ComplexityBridge.TM2ContextMapBoundary
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNFLiteralConstructor (framedBits delimit_prefix)

inductive Stack where | context | payload | scratch | core | accum deriving DecidableEq
inductive Label where | scanPayload | restorePayload | scanContext | restoreContext | ready | emit | done deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.context,.payload,.scratch,.core,.accum] (by intro k; cases k <;> simp)
instance : Fintype Label := Fintype.ofList [.scanPayload,.restorePayload,.scanContext,.restoreContext,.ready,.emit,.done] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .scanPayload => .pop .payload (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scanPayload)))
        (.goto (fun _ => .restorePayload)))
  | .restorePayload => .pop .scratch (fun _ h => h)
      (.branch Option.isSome (.push .core (fun v => v.getD false) (.goto (fun _ => .restorePayload)))
        (.push .core (fun _ => false) (.goto (fun _ => .scanContext))))
  | .scanContext => .pop .context (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scanContext)))
        (.goto (fun _ => .restoreContext)))
  | .restoreContext => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .context (fun v => v.getD false)
          (.push .core (fun v => v.getD false) (.push .core (fun _ => true) (.goto (fun _ => .restoreContext)))))
        (.load (fun _ => none) (.goto (fun _ => .ready))))
  | .ready => .goto (fun _ => .ready)
  | .emit => .pop .core (fun _ h => h)
      (.branch Option.isSome
        (.push .accum (fun _ => true) (.push .accum (fun v => v.getD false) (.goto (fun _ => .emit))))
        (.push .accum (fun _ => false) (.load (fun _ => none) (.goto (fun _ => .done)))))
  | .done => .goto (fun _ => .done)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .payload
  k₁ := .core
  Γ := fun _ => Bool
  Λ := Label
  main := .scanPayload
  σ := Option Bool
  initialState := none
  m := program

def stackVals (ctx payload scratch core acc : List Bool) : Stack → List Bool
  | .context => ctx | .payload => payload | .scratch => scratch | .core => core | .accum => acc

def cfg (l : Label) (v : Option Bool) (ctx payload scratch core acc : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals ctx payload scratch core acc⟩

theorem scanPayload_cons (v : Option Bool) (b : Bool) (ctx payload scratch core acc : List Bool) :
    machine.step (cfg .scanPayload v ctx (b::payload) scratch core acc) =
      some (cfg .scanPayload (some b) ctx payload (b::scratch) core acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scanPayload_nil (v : Option Bool) (ctx scratch core acc : List Bool) :
    machine.step (cfg .scanPayload v ctx [] scratch core acc) =
      some (cfg .restorePayload none ctx [] scratch core acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restorePayload_cons (v : Option Bool) (b : Bool) (ctx scratch core acc : List Bool) :
    machine.step (cfg .restorePayload v ctx [] (b::scratch) core acc) =
      some (cfg .restorePayload (some b) ctx [] scratch (b::core) acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restorePayload_nil (v : Option Bool) (ctx core acc : List Bool) :
    machine.step (cfg .restorePayload v ctx [] [] core acc) =
      some (cfg .scanContext none ctx [] [] (false::core) acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scanContext_cons (v : Option Bool) (b : Bool) (ctx scratch core acc : List Bool) :
    machine.step (cfg .scanContext v (b::ctx) [] scratch core acc) =
      some (cfg .scanContext (some b) ctx [] (b::scratch) core acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scanContext_nil (v : Option Bool) (scratch core acc : List Bool) :
    machine.step (cfg .scanContext v [] [] scratch core acc) =
      some (cfg .restoreContext none [] [] scratch core acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restoreContext_cons (v : Option Bool) (b : Bool) (ctx scratch core acc : List Bool) :
    machine.step (cfg .restoreContext v ctx [] (b::scratch) core acc) =
      some (cfg .restoreContext (some b) (b::ctx) [] scratch (true::b::core) acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restoreContext_nil (v : Option Bool) (ctx core acc : List Bool) :
    machine.step (cfg .restoreContext v ctx [] [] core acc) = some (cfg .ready none ctx [] [] core acc) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem emit_cons (v : Option Bool) (b : Bool) (ctx core acc : List Bool) :
    machine.step (cfg .emit v ctx [] [] (b::core) acc) =
      some (cfg .emit (some b) ctx [] [] core (b::true::acc)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem emit_nil (v : Option Bool) (ctx acc : List Bool) :
    machine.step (cfg .emit v ctx [] [] [] acc) = some (cfg .done none ctx [] [] [] (false::acc)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scanPayload_run (payload ctx scratch core acc : List Bool) (v : Option Bool) :
    runSteps machine.step (payload.length+1) (cfg .scanPayload v ctx payload scratch core acc) =
      some (cfg .restorePayload none ctx [] (payload.reverse++scratch) core acc) := by
  induction payload generalizing scratch v with
  | nil => exact scanPayload_nil v ctx scratch core acc
  | cons b payload ih =>
    rw [List.length_cons,show payload.length+1+1 = (payload.length+1)+1 by omega,runSteps_front,scanPayload_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restorePayload_run (scratch ctx core acc : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restorePayload v ctx [] scratch core acc) =
      some (cfg .scanContext none ctx [] [] (false::(scratch.reverse++core)) acc) := by
  induction scratch generalizing core v with
  | nil => exact restorePayload_nil v ctx core acc
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restorePayload_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::core) (some b)

theorem scanContext_run (ctx scratch core acc : List Bool) (v : Option Bool) :
    runSteps machine.step (ctx.length+1) (cfg .scanContext v ctx [] scratch core acc) =
      some (cfg .restoreContext none [] [] (ctx.reverse++scratch) core acc) := by
  induction ctx generalizing scratch v with
  | nil => exact scanContext_nil v scratch core acc
  | cons b ctx ih =>
    rw [List.length_cons,show ctx.length+1+1 = (ctx.length+1)+1 by omega,runSteps_front,scanContext_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restoreContext_run (scratch ctx core acc : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restoreContext v ctx [] scratch core acc) =
      some (cfg .ready none (scratch.reverse++ctx) [] [] (framedBits scratch.reverse++core) acc) := by
  induction scratch generalizing ctx core v with
  | nil => simpa [runSteps,framedBits] using restoreContext_nil v ctx core acc
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restoreContext_cons]
    simpa [framedBits,List.reverse_cons,List.flatMap_append,List.append_assoc] using ih (b::ctx) (true::b::core) (some b)

/-- The exact finite preparation segment retains the context and accumulator
and writes the pair encoding to the core-input stack. -/
theorem prepare (ctx payload acc : List Bool) :
    runSteps machine.step (2*payload.length+2*ctx.length+4)
      (cfg .scanPayload none ctx payload [] [] acc) =
      some (cfg .ready none ctx [] [] (BitstringEncoding.delimit ctx++payload) acc) := by
  have hp := scanPayload_run payload ctx [] [] acc none
  simp only [List.append_nil] at hp
  have hr := restorePayload_run payload.reverse ctx [] acc none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  have hc := scanContext_run ctx [] (false::payload) acc none
  simp only [List.append_nil] at hc
  have hrc := restoreContext_run ctx.reverse [] (false::payload) acc none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hrc
  have hn : 2*payload.length+2*ctx.length+4 =
      (payload.length+1)+((payload.length+1)+((ctx.length+1)+(ctx.length+1))) := by omega
  rw [hn,runSteps_add,hp]
  change runSteps machine.step ((payload.length+1)+((ctx.length+1)+(ctx.length+1))) _ = _
  rw [runSteps_add,hr]
  change runSteps machine.step ((ctx.length+1)+(ctx.length+1)) _ = _
  rw [runSteps_add,hc]
  simpa [delimit_prefix,List.append_assoc] using hrc

/-- The same boundary is exactly the pinned pair encoding for typed inputs. -/
theorem prepare_encoded {κ α : Type} [BitstringEncoding κ] [BitstringEncoding α]
    (ctx : κ) (item : α) (acc : List Bool) :
    runSteps machine.step (2*(BitstringEncoding.bitEncode item).length+2*(BitstringEncoding.bitEncode ctx).length+4)
      (cfg .scanPayload none (BitstringEncoding.bitEncode ctx) (BitstringEncoding.bitEncode item) [] [] acc) =
      some (cfg .ready none (BitstringEncoding.bitEncode ctx) [] [] (BitstringEncoding.bitEncode (ctx,item)) acc) := by
  exact prepare _ _ _

theorem emit_run (result ctx acc : List Bool) (v : Option Bool) :
    runSteps machine.step (result.length+1) (cfg .emit v ctx [] [] result acc) =
      some (cfg .done none ctx [] [] [] ((BitstringEncoding.delimit result).reverse++acc)) := by
  induction result generalizing acc v with
  | nil => simpa [runSteps,BitstringEncoding.delimit] using emit_nil v ctx acc
  | cons b result ih =>
    rw [List.length_cons,show result.length+1+1 = (result.length+1)+1 by omega,runSteps_front,emit_cons]
    simpa [BitstringEncoding.delimit,List.reverse_cons,List.append_assoc] using ih (b::true::acc) (some b)

/-- Specialized guard-item input boundary: the encoded index remains on its
own stack, and the core receives exactly the canonical pair. -/
theorem prepare_guard (i : Nat) (c : Shared.ComplexityBridge.CNF.Clause) (acc : List Bool) :
    runSteps machine.step (2*(BitstringEncoding.bitEncode c).length+2*(BitstringEncoding.bitEncode i).length+4)
      (cfg .scanPayload none (BitstringEncoding.bitEncode i) (BitstringEncoding.bitEncode c) [] [] acc) =
      some (cfg .ready none (BitstringEncoding.bitEncode i) [] [] (BitstringEncoding.bitEncode (i,c)) acc) :=
  prepare_encoded i c acc

/-- After an independently verified guard-clause execution, its returned
bytes can be framed and accumulated with all transfer steps charged. -/
theorem emit_guard (i : Nat) (c : Shared.ComplexityBridge.CNF.Clause) (acc : List Bool) :
    runSteps machine.step
      ((BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.guardClause i c)).length+1)
      (cfg .emit none (BitstringEncoding.bitEncode i) [] []
        (BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.guardClause i c)) acc) =
      some (cfg .done none (BitstringEncoding.bitEncode i) [] [] []
        ((BitstringEncoding.delimit (BitstringEncoding.bitEncode
          (Shared.ComplexityBridge.CNFDisjunction.guardClause i c))).reverse++acc)) :=
  emit_run _ _ _ none

namespace Fixtures
example : runSteps machine.step 4 (cfg .scanPayload none [] [] [] [] []) =
    some (cfg .ready none [] [] [] [false] []) := by
  simpa [BitstringEncoding.delimit] using prepare [] [] []
example : runSteps machine.step 2 (cfg .emit none [] [] [] [true] []) =
    some (cfg .done none [] [] [] [] [false,true,true]) := by
  simpa [BitstringEncoding.delimit] using emit_run [true] [] [] none
end Fixtures

end Shared.ComplexityBridge.TM2ContextMapBoundary
