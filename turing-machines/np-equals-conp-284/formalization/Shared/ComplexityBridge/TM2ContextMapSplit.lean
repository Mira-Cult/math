import Shared.ComplexityBridge.TM2ContextMapBoundary

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! A finite formula-item splitter joined to the existing pair-preparation
machine. It reads one delimited item, preserves the remaining stream and the
accumulator, then constructs the canonical context/item input. This does not
run the item evaluator or complete the traversal. -/
namespace Shared.ComplexityBridge.TM2ContextMapSplit
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev B := Shared.ComplexityBridge.TM2ContextMapBoundary.machine
abbrev BK := Shared.ComplexityBridge.TM2ContextMapBoundary.Stack
abbrev BL := Shared.ComplexityBridge.TM2ContextMapBoundary.Label
inductive Parse where | header | data | restore | done | reject deriving DecidableEq
instance : Fintype Parse := Fintype.ofList [.header,.data,.restore,.done,.reject] (by intro l; cases l <;> simp)
abbrev Key := BK ⊕ Unit
abbrev Label := BL ⊕ Parse

def stackVals (S : BK → List Bool) (tail : List Bool) : Key → List Bool
  | .inl k => S k | .inr _ => tail

def embed (q : B.Cfg) (tail : List Bool) : Cfg (fun _ : Key => Bool) Label (Option Bool) :=
  ⟨q.l.map Sum.inl,q.var,stackVals q.stk tail⟩

def lift : B.Stmt → Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .push j f q => .push (.inl j) f (lift q)
  | .peek j f q => .peek (.inl j) f (lift q)
  | .pop j f q => .pop (.inl j) f (lift q)
  | .load f q => .load f (lift q)
  | .branch f q r => .branch f (lift q) (lift r)
  | .goto f => .goto (Sum.inl ∘ f)
  | .halt => .halt

theorem update_inner (S : BK → List Bool) (tail : List Bool) (j : BK) (xs : List Bool) :
    Function.update (stackVals S tail) (.inl j) xs = stackVals (Function.update S j xs) tail := by
  funext k; cases k with
  | inl k => by_cases h : k = j <;> simp [stackVals,Function.update,h]
  | inr k => simp [stackVals,Function.update,Sum.inl.injEq]

theorem lift_aux (q : B.Stmt) (v : Option Bool) (S : BK → List Bool) (tail : List Bool) :
    stepAux (lift q) v (stackVals S tail) = embed (stepAux q v S) tail := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => simp only [lift,stepAux]; rw [update_inner]; exact ih _ _
  | push j f q ih => simp only [lift,stepAux]; rw [update_inner]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .inl l => lift (Shared.ComplexityBridge.TM2ContextMapBoundary.program l)
  | .inr .header => .pop (.inr ()) (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true) (.goto (fun _ => .inr .data)) (.goto (fun _ => .inr .restore)))
        (.load (fun _ => none) (.goto (fun _ => .inr .done))))
  | .inr .data => .pop (.inr ()) (fun _ h => h)
      (.branch Option.isSome (.push (.inl .scratch) (fun v => v.getD false) (.goto (fun _ => .inr .header)))
        (.goto (fun _ => .inr .reject)))
  | .inr .restore => .pop (.inl .scratch) (fun _ h => h)
      (.branch Option.isSome (.push (.inl .payload) (fun v => v.getD false) (.goto (fun _ => .inr .restore)))
        (.load (fun _ => none) (.goto (fun _ => .inl .scanPayload))))
  | .inr .done => .goto (fun _ => .inr .done)
  | .inr .reject => .goto (fun _ => .inr .reject)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inr ()
  k₁ := .inl .core
  Γ := fun _ => Bool
  Λ := Label
  main := .inr .header
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Label) (v : Option Bool) (ctx payload scratch core acc tail : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals (Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals ctx payload scratch core acc) tail⟩

theorem header_true (v : Option Bool) (ctx payload scratch core acc tail : List Bool) :
    machine.step (cfg (.inr .header) v ctx payload scratch core acc (true::tail)) =
      some (cfg (.inr .data) (some true) ctx payload scratch core acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [cfg,stackVals,Function.update,Sum.inl.injEq]

theorem header_false (v : Option Bool) (ctx payload scratch core acc tail : List Bool) :
    machine.step (cfg (.inr .header) v ctx payload scratch core acc (false::tail)) =
      some (cfg (.inr .restore) (some false) ctx payload scratch core acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [cfg,stackVals,Function.update,Sum.inl.injEq]

theorem header_nil (v : Option Bool) (ctx payload scratch core acc : List Bool) :
    machine.step (cfg (.inr .header) v ctx payload scratch core acc []) =
      some (cfg (.inr .done) none ctx payload scratch core acc []) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [cfg,stackVals,Function.update,Sum.inl.injEq]

theorem data_cons (v : Option Bool) (b : Bool) (ctx payload scratch core acc tail : List Bool) :
    machine.step (cfg (.inr .data) v ctx payload scratch core acc (b::tail)) =
      some (cfg (.inr .header) (some b) ctx payload (b::scratch) core acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [cfg,stackVals,Function.update,Sum.inl.injEq]

theorem restore_cons (v : Option Bool) (b : Bool) (ctx payload scratch core acc tail : List Bool) :
    machine.step (cfg (.inr .restore) v ctx payload (b::scratch) core acc tail) =
      some (cfg (.inr .restore) (some b) ctx (b::payload) scratch core acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [cfg,stackVals,Function.update,Sum.inl.injEq]

theorem restore_nil (v : Option Bool) (ctx payload core acc tail : List Bool) :
    machine.step (cfg (.inr .restore) v ctx payload [] core acc tail) =
      some (cfg (.inl .scanPayload) none ctx payload [] core acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl k => cases k <;> simp [machine,cfg,stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [cfg,stackVals,Function.update,Sum.inl.injEq]

theorem scan_run (bits ctx payload scratch core acc tail : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (2*bits.length)
      (cfg (.inr .header) v ctx payload scratch core acc (BitstringEncoding.delimit bits ++ tail)) =
      some (cfg (.inr .header) v' ctx payload (bits.reverse++scratch) core acc (false::tail)) := by
  induction bits generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit]⟩
  | cons b bits ih =>
    obtain ⟨v',h⟩ := ih (b::scratch) (some b)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    rw [show 2*(bits.length+1) = (2*bits.length+1)+1 by omega,runSteps_front,header_true]
    change runSteps machine.step (2*bits.length+1)
      (cfg (.inr .data) (some true) ctx payload scratch core acc (b::(BitstringEncoding.delimit bits++tail))) = _
    rw [runSteps_front,data_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore_run (scratch ctx payload core acc tail : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg (.inr .restore) v ctx payload scratch core acc tail) =
      some (cfg (.inl .scanPayload) none ctx (scratch.reverse++payload) [] core acc tail) := by
  induction scratch generalizing payload v with
  | nil => exact restore_nil v ctx payload core acc tail
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::payload) (some b)

theorem split_run (bits ctx acc tail : List Bool) :
    runSteps machine.step (3*bits.length+2)
      (cfg (.inr .header) none ctx [] [] [] acc (BitstringEncoding.delimit bits++tail)) =
      some (cfg (.inl .scanPayload) none ctx bits [] [] acc tail) := by
  obtain ⟨v,hs⟩ := scan_run bits ctx [] [] [] acc tail none
  simp only [List.append_nil] at hs
  have hr := restore_run bits.reverse ctx [] [] acc tail (some false)
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hr
  rw [show 3*bits.length+2 = 2*bits.length+(1+(bits.length+1)) by omega,runSteps_add,hs]
  change runSteps machine.step (1+(bits.length+1)) (cfg (.inr .header) v ctx [] bits.reverse [] acc (false::tail)) = _
  rw [Nat.add_comm 1 _,runSteps_front,header_false]
  exact hr

theorem core_step (q : B.Cfg) (tail : List Bool) (h : q.l ≠ none) :
    machine.step (embed q tail) = (B.step q).map (fun r => embed r tail) := by
  cases q with
  | mk l v S => cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (lift (Shared.ComplexityBridge.TM2ContextMapBoundary.program l)) v (stackVals S tail)) = _
      rw [lift_aux]; rfl

theorem core_run (n : Nat) (q r : B.Cfg) (tail : List Bool) (h : runSteps B.step n q = some r) :
    runSteps machine.step n (embed q tail) = some (embed r tail) := by
  induction n generalizing q with
  | zero => change some q = some r at h; cases h; rfl
  | succ n ih =>
    rw [runSteps_front] at h
    change (B.step q).bind (runSteps B.step n) = some r at h
    cases hs : B.step q with
    | none => rw [hs] at h; contradiction
    | some q' =>
      have ha : q.l ≠ none := by
        intro hl
        have hn : B.step q = none := by cases q with | mk l v S => cases l with | none => rfl | some l => simp at hl
        rw [hn] at hs; contradiction
      rw [hs] at h
      rw [runSteps_front,core_step q tail ha,hs]
      exact ih q' h

/-- Read one framed item and prepare the canonical pair, preserving the exact
unread stream and accumulated output. All segment steps are charged. -/
theorem split_prepare (ctx bits acc tail : List Bool) :
    runSteps machine.step (5*bits.length+2*ctx.length+6)
      (cfg (.inr .header) none ctx [] [] [] acc (BitstringEncoding.delimit bits++tail)) =
      some (cfg (.inl .ready) none ctx [] [] (BitstringEncoding.delimit ctx++bits) acc tail) := by
  have hs := split_run bits ctx acc tail
  have hp := Shared.ComplexityBridge.TM2ContextMapBoundary.prepare ctx bits acc
  have hp' := core_run _ _ _ tail hp
  change runSteps machine.step (2*bits.length+2*ctx.length+4)
    (cfg (.inl .scanPayload) none ctx bits [] [] acc tail) =
      some (cfg (.inl .ready) none ctx [] [] (BitstringEncoding.delimit ctx++bits) acc tail) at hp'
  rw [show 5*bits.length+2*ctx.length+6 = (3*bits.length+2)+(2*bits.length+2*ctx.length+4) by omega,
    runSteps_add,hs]
  exact hp'

/-- One step of the intended typed list traversal: the serialized tail is
unchanged and the core input is precisely the pinned pair encoding. -/
theorem split_prepare_encoded {κ α : Type} [BitstringEncoding κ] [BitstringEncoding α]
    (ctx : κ) (item : α) (rest : List α) (acc : List Bool) :
    runSteps machine.step
      (5*(BitstringEncoding.bitEncode item).length+2*(BitstringEncoding.bitEncode ctx).length+6)
      (cfg (.inr .header) none (BitstringEncoding.bitEncode ctx) [] [] [] acc
        (BitstringEncoding.bitEncode (item::rest))) =
      some (cfg (.inl .ready) none (BitstringEncoding.bitEncode ctx) [] []
        (BitstringEncoding.bitEncode (ctx,item)) acc (BitstringEncoding.bitEncode rest)) := by
  exact split_prepare _ _ _ _

namespace Fixtures
example : runSteps machine.step 6 (cfg (.inr .header) none [] [] [] [] [] [false]) =
    some (cfg (.inl .ready) none [] [] [] [false] [] []) := by
  simpa [BitstringEncoding.delimit] using split_prepare [] [] [] []
example : runSteps machine.step 11 (cfg (.inr .header) none [] [] [] [] [true] [true,false,false,true]) =
    some (cfg (.inl .ready) none [] [] [] [false,false] [true] [true]) := by
  simpa [BitstringEncoding.delimit] using split_prepare [] [false] [true] [true]
example : machine.step (cfg (.inr .header) none [] [] [] [] [] []) =
    some (cfg (.inr .done) none [] [] [] [] [] []) := header_nil _ _ _ _ _ _
end Fixtures
end Shared.ComplexityBridge.TM2ContextMapSplit
