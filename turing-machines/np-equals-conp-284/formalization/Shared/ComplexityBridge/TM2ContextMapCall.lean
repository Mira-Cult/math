import Shared.ComplexityBridge.TM2ContextMapSplit
import Shared.ComplexityBridge.TM2Compose

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Embed the list splitter and an arbitrary finite item machine in one
finite TM2. The entry and exit transfers use explicit scratch and core stacks;
all stacks carrying the unread list, context, and accumulator are retained.
The control program is not yet a proved complete list traversal. -/
namespace Shared.ComplexityBridge.TM2ContextMapCall
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev S := Shared.ComplexityBridge.TM2ContextMapSplit.machine
abbrev SK := Shared.ComplexityBridge.TM2ContextMapSplit.Key
abbrev SL := Shared.ComplexityBridge.TM2ContextMapSplit.Label
abbrev BK := Shared.ComplexityBridge.TM2ContextMapBoundary.Stack
abbrev BL := Shared.ComplexityBridge.TM2ContextMapBoundary.Label
abbrev Parse := Shared.ComplexityBridge.TM2ContextMapSplit.Parse

abbrev Key (f : Turing.FinTM2) := SK ⊕ f.K
def Alphabet (f : Turing.FinTM2) : Key f → Type
  | .inl _ => Bool | .inr k => f.Γ k
inductive Control where | load | restore | drain | unload deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.load,.restore,.drain,.unload] (by intro l; cases l <;> simp)
abbrev Label (f : Turing.FinTM2) := SL ⊕ (Control ⊕ f.Λ)
abbrev State (f : Turing.FinTM2) := Option Bool ⊕ f.σ

def srcState (f : Turing.FinTM2) : State f → Option Bool | .inl v => v | .inr _ => none
def itemState (f : Turing.FinTM2) : State f → f.σ | .inl _ => f.initialState | .inr v => v

def stackVals (f : Turing.FinTM2) (A : SK → List Bool) (F : (k : f.K) → List (f.Γ k)) :
    (k : Key f) → List (Alphabet f k)
  | .inl k => A k | .inr k => F k

theorem update_src (f : Turing.FinTM2) (A : SK → List Bool) (F : (k : f.K) → List (f.Γ k))
    (j : SK) (xs : List Bool) :
    Function.update (stackVals f A F) (.inl j) xs = stackVals f (Function.update A j xs) F := by
  funext k; cases k with
  | inl k =>
    by_cases h : k = j
    · subst k; simp [stackVals]
    · have hh : (Sum.inl k : Key f) ≠ .inl j := by simpa using h
      simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]
  | inr k => simp [stackVals,Function.update]

theorem update_item (f : Turing.FinTM2) (A : SK → List Bool) (F : (k : f.K) → List (f.Γ k))
    (j : f.K) (xs : List (f.Γ j)) :
    Function.update (stackVals f A F) (.inr j) xs = stackVals f A (Function.update F j xs) := by
  funext k; cases k with
  | inl k => simp [stackVals,Function.update]
  | inr k =>
    by_cases h : k = j
    · subst k; simp [stackVals]
    · have hh : (Sum.inr k : Key f) ≠ .inr j := by simpa using h
      simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]

def srcEmbed (f : Turing.FinTM2) (q : S.Cfg) (F : (k : f.K) → List (f.Γ k)) :
    Cfg (Alphabet f) (Label f) (State f) :=
  ⟨q.l.map Sum.inl,.inl q.var,stackVals f q.stk F⟩

def itemEmbed (f : Turing.FinTM2) (A : SK → List Bool) (q : f.Cfg) :
    Cfg (Alphabet f) (Label f) (State f) :=
  match q.l with
  | some l => ⟨some (.inr (.inr l)),.inr q.var,stackVals f A q.stk⟩
  | none => ⟨some (.inr (.inl .drain)),.inl none,stackVals f A q.stk⟩

def liftSrc (f : Turing.FinTM2) : S.Stmt → Stmt (Alphabet f) (Label f) (State f)
  | .push j h q => .push (.inl j) (fun v => h (srcState f v)) (liftSrc f q)
  | .peek j h q => .peek (.inl j) (fun v x => .inl (h (srcState f v) x)) (liftSrc f q)
  | .pop j h q => .pop (.inl j) (fun v x => .inl (h (srcState f v) x)) (liftSrc f q)
  | .load h q => .load (fun v => .inl (h (srcState f v))) (liftSrc f q)
  | .branch h q r => .branch (fun v => h (srcState f v)) (liftSrc f q) (liftSrc f r)
  | .goto h => .goto (fun v => .inl (h (srcState f v)))
  | .halt => .halt

def liftItem (f : Turing.FinTM2) : f.Stmt → Stmt (Alphabet f) (Label f) (State f)
  | .push j h q => .push (.inr j) (fun v => h (itemState f v)) (liftItem f q)
  | .peek j h q => .peek (.inr j) (fun v x => .inr (h (itemState f v) x)) (liftItem f q)
  | .pop j h q => .pop (.inr j) (fun v x => .inr (h (itemState f v) x)) (liftItem f q)
  | .load h q => .load (fun v => .inr (h (itemState f v))) (liftItem f q)
  | .branch h q r => .branch (fun v => h (itemState f v)) (liftItem f q) (liftItem f r)
  | .goto h => .goto (fun v => .inr (.inr (h (itemState f v))))
  | .halt => .load (fun _ => .inl none) (.goto (fun _ => .inr (.inl .drain)))

theorem liftSrc_aux (f : Turing.FinTM2) (q : S.Stmt) (v : Option Bool) (A : SK → List Bool)
    (F : (k : f.K) → List (f.Γ k)) :
    stepAux (liftSrc f q) (.inl v) (stackVals f A F) = srcEmbed f (stepAux q v A) F := by
  induction q generalizing v A with
  | halt => rfl
  | goto h => rfl
  | load h q ih => exact ih _ _
  | peek j h q ih => exact ih _ _
  | push j h q ih => simp only [liftSrc,stepAux,srcState]; rw [update_src]; exact ih _ _
  | pop j h q ih => simp only [liftSrc,stepAux,srcState]; rw [update_src]; exact ih _ _
  | branch h q r ihq ihr => by_cases hh : h v <;> simp [liftSrc,stepAux,srcState,hh,ihq,ihr]

theorem liftItem_aux (f : Turing.FinTM2) (q : f.Stmt) (v : f.σ) (A : SK → List Bool)
    (F : (k : f.K) → List (f.Γ k)) :
    stepAux (liftItem f q) (.inr v) (stackVals f A F) = itemEmbed f A (stepAux q v F) := by
  induction q generalizing v F with
  | halt => rfl
  | goto h => rfl
  | load h q ih => exact ih _ _
  | peek j h q ih => exact ih _ _
  | push j h q ih => simp only [liftItem,stepAux,itemState]; rw [update_item]; exact ih _ _
  | pop j h q ih => simp only [liftItem,stepAux,itemState]; rw [update_item]; exact ih _ _
  | branch h q r ihq ihr => by_cases hh : h v <;> simp [liftItem,stepAux,itemState,hh,ihq,ihr]

def program (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :
    Label f → Stmt (Alphabet f) (Label f) (State f)
  | .inl (.inl .ready) => .load (fun _ => .inl none) (.goto (fun _ => .inr (.inl .load)))
  | .inl (.inl .done) => .goto (fun _ => .inl (.inl .done))
  | .inl l => liftSrc f (S.m l)
  | .inr (.inl .load) => .pop (.inl (.inl .core)) (fun _ h => .inl h)
      (.branch (fun v => (srcState f v).isSome)
        (.push (.inl (.inl .scratch)) (fun v => (srcState f v).getD false) (.goto (fun _ => .inr (.inl .load))))
        (.goto (fun _ => .inr (.inl .restore))))
  | .inr (.inl .restore) => .pop (.inl (.inl .scratch)) (fun _ h => .inl h)
      (.branch (fun v => (srcState f v).isSome)
        (.push (.inr f.k₀) (fun v => inp.symm ((srcState f v).getD false)) (.goto (fun _ => .inr (.inl .restore))))
        (.load (fun _ => .inr f.initialState) (.goto (fun _ => .inr (.inr f.main)))))
  | .inr (.inl .drain) => .pop (.inr f.k₁) (fun _ h => .inl (h.map out))
      (.branch (fun v => (srcState f v).isSome)
        (.push (.inl (.inl .scratch)) (fun v => (srcState f v).getD false) (.goto (fun _ => .inr (.inl .drain))))
        (.goto (fun _ => .inr (.inl .unload))))
  | .inr (.inl .unload) => .pop (.inl (.inl .scratch)) (fun _ h => .inl h)
      (.branch (fun v => (srcState f v).isSome)
        (.push (.inl (.inl .core)) (fun v => (srcState f v).getD false) (.goto (fun _ => .inr (.inl .unload))))
        (.load (fun _ => .inl none) (.goto (fun _ => .inl (.inl .emit)))))
  | .inr (.inr l) => liftItem f (f.m l)

def machine (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) : Turing.FinTM2 := by
  letI := f.kFin; letI := f.ΛFin; letI := f.σFin
  exact {
    K := Key f
    k₀ := .inl (.inr ())
    k₁ := .inl (.inl .accum)
    Γ := Alphabet f
    Λ := Label f
    main := .inl (.inr .header)
    σ := State f
    initialState := .inl none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := program f inp out }

def terminal (q : S.Cfg) : Prop := q.l = some (.inl .ready)
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _

theorem stable (q : S.Cfg) (h : terminal q) : S.step q = some q := by
  cases q with
  | mk l v A => change l = some (.inl .ready) at h; subst l; rfl

theorem src_step (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (F : (k : f.K) → List (f.Γ k)) (q : S.Cfg) (h : ¬ terminal q) :
    (machine f inp out).step (srcEmbed f q F) = (S.step q).map (fun r => srcEmbed f r F) := by
  cases q with
  | mk l v A => cases l with
    | none => rfl
    | some l =>
      cases l with
      | inl l =>
        cases l with
        | ready => exact False.elim (h rfl)
        | done => rfl
        | scanPayload | restorePayload | scanContext | restoreContext | emit =>
          change some (stepAux (liftSrc f (S.m _)) (.inl v) (stackVals f A F)) = _
          rw [liftSrc_aux]; rfl
      | inr l =>
        cases l <;> change some (stepAux (liftSrc f (S.m _)) (.inl v) (stackVals f A F)) = _ <;> rw [liftSrc_aux] <;> rfl

theorem item_step (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (A : SK → List Bool) (q : f.Cfg) (h : q.l ≠ none) :
    (machine f inp out).step (itemEmbed f A q) = (f.step q).map (fun r => itemEmbed f A r) := by
  cases q with
  | mk l v F => cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (liftItem f (f.m l)) (.inr v) (stackVals f A F)) = _
      rw [liftItem_aux]; rfl

theorem item_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (A : SK → List Bool) (n : Nat) (q r : f.Cfg) (h : runSteps f.step n q = some r) :
    runSteps (machine f inp out).step n (itemEmbed f A q) = some (itemEmbed f A r) := by
  induction n generalizing q with
  | zero => change some q = some r at h; cases h; rfl
  | succ n ih =>
    rw [runSteps_front] at h
    change (f.step q).bind (runSteps f.step n) = some r at h
    cases hs : f.step q with
    | none => rw [hs] at h; contradiction
    | some q' =>
      have ha : q.l ≠ none := by
        intro hl
        have hn : f.step q = none := by cases q with | mk l v F => cases l with | none => rfl | some l => simp at hl
        rw [hn] at hs; contradiction
      rw [hs] at h
      rw [runSteps_front,item_step f inp out A q ha,hs]
      exact ih q' h


def workStacks (ctx scratch core acc tail : List Bool) : SK → List Bool :=
  (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .ready) none ctx [] scratch core acc tail).stk

theorem work_update_core (ctx scratch core acc tail xs : List Bool) :
    Function.update (workStacks ctx scratch core acc tail) (.inl .core) xs =
      workStacks ctx scratch xs acc tail := by
  funext k; cases k with
  | inl k => cases k <;> simp [workStacks,Shared.ComplexityBridge.TM2ContextMapSplit.cfg,
      Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,
      Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [workStacks,Shared.ComplexityBridge.TM2ContextMapSplit.cfg,
      Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem work_update_scratch (ctx scratch core acc tail xs : List Bool) :
    Function.update (workStacks ctx scratch core acc tail) (.inl .scratch) xs =
      workStacks ctx xs core acc tail := by
  funext k; cases k with
  | inl k => cases k <;> simp [workStacks,Shared.ComplexityBridge.TM2ContextMapSplit.cfg,
      Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,
      Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [workStacks,Shared.ComplexityBridge.TM2ContextMapSplit.cfg,
      Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

def loadCfg (f : Turing.FinTM2) (l : Control) (v : Option Bool)
    (ctx scratch core acc tail : List Bool) (ys : List (f.Γ f.k₀)) :
    Cfg (Alphabet f) (Label f) (State f) :=
  ⟨some (.inr (.inl l)),.inl v,stackVals f (workStacks ctx scratch core acc tail) (Turing.initList f ys).stk⟩

theorem ready_dispatch (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx core acc tail : List Bool) :
    (machine f inp out).step
      (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .ready) none ctx [] [] core acc tail)
        (Turing.initList f []).stk) = some (loadCfg f .load none ctx [] core acc tail []) := rfl

theorem load_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx scratch core acc tail : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (loadCfg f .load v ctx scratch (b::core) acc tail ys) =
      some (loadCfg f .load (some b) ctx (b::scratch) core acc tail ys) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [update_src,work_update_core,update_src,work_update_scratch]
  rfl

theorem load_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx scratch acc tail : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (loadCfg f .load v ctx scratch [] acc tail ys) =
      some (loadCfg f .restore none ctx scratch [] acc tail ys) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [update_src,work_update_core]
  rfl

theorem restore_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx scratch acc tail : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (loadCfg f .restore v ctx (b::scratch) [] acc tail ys) =
      some (loadCfg f .restore (some b) ctx scratch [] acc tail (inp.symm b::ys)) := by
  have hin : (Turing.initList f ys).stk f.k₀ = ys := by simp [Turing.initList]
  change some (Cfg.mk (some (.inr (.inl .restore)) : Option (Label f)) (.inl (some b) : State f)
    (Function.update (Function.update
      (stackVals f (workStacks ctx (b::scratch) [] acc tail) (Turing.initList f ys).stk)
      (.inl (.inl .scratch)) scratch) (.inr f.k₀) (inp.symm b :: (Turing.initList f ys).stk f.k₀))) = _
  rw [hin]
  congr 1; congr 1
  rw [update_src,work_update_scratch,update_item,Shared.ComplexityBridge.TM2Compose.initStacks_update]

theorem restore_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx acc tail : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (loadCfg f .restore v ctx [] [] acc tail ys) =
      some (itemEmbed f (workStacks ctx [] [] acc tail) (Turing.initList f ys)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [update_src,work_update_scratch]
  rfl

theorem load_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (core ctx scratch acc tail : List Bool) (ys : List (f.Γ f.k₀)) (v : Option Bool) :
    runSteps (machine f inp out).step (core.length+1)
      (loadCfg f .load v ctx scratch core acc tail ys) =
      some (loadCfg f .restore none ctx (core.reverse++scratch) [] acc tail ys) := by
  induction core generalizing scratch v with
  | nil => exact load_nil f inp out v ctx scratch acc tail ys
  | cons b core ih =>
    rw [List.length_cons,show core.length+1+1 = (core.length+1)+1 by omega,runSteps_front,load_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem restore_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (scratch ctx acc tail : List Bool) (ys : List (f.Γ f.k₀)) (v : Option Bool) :
    runSteps (machine f inp out).step (scratch.length+1)
      (loadCfg f .restore v ctx scratch [] acc tail ys) =
      some (itemEmbed f (workStacks ctx [] [] acc tail)
        (Turing.initList f (scratch.reverse.map inp.symm++ys))) := by
  induction scratch generalizing ys v with
  | nil => exact restore_nil f inp out v ctx acc tail ys
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using ih (inp.symm b::ys) (some b)

/-- Transfer the prepared bitstring to a freshly initialized finite evaluator,
without changing the preserved context, accumulator, or unread stream. -/
theorem load_item (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (bits ctx acc tail : List Bool) :
    runSteps (machine f inp out).step (2*bits.length+3)
      (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .ready) none ctx [] [] bits acc tail)
        (Turing.initList f []).stk) =
      some (itemEmbed f (workStacks ctx [] [] acc tail) (Turing.initList f (bits.map inp.symm))) := by
  have hl := load_run f inp out bits ctx [] acc tail [] none
  simp only [List.append_nil] at hl
  have hr := restore_run f inp out bits.reverse ctx acc tail [] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  rw [show 2*bits.length+3 = 1+((bits.length+1)+(bits.length+1)) by omega, Nat.add_comm 1 _,
    runSteps_front,ready_dispatch]
  change runSteps (machine f inp out).step ((bits.length+1)+(bits.length+1))
    (loadCfg f .load none ctx [] bits acc tail []) = _
  rw [runSteps_add,hl]
  exact hr


def drainCfg (f : Turing.FinTM2) (l : Control) (v : Option Bool)
    (ctx scratch core acc tail : List Bool) (xs : List (f.Γ f.k₁)) :
    Cfg (Alphabet f) (Label f) (State f) :=
  ⟨some (.inr (.inl l)),.inl v,stackVals f (workStacks ctx scratch core acc tail) (Turing.haltList f xs).stk⟩

theorem drain_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (a : f.Γ f.k₁) (ctx scratch core acc tail : List Bool) (xs : List (f.Γ f.k₁)) :
    (machine f inp out).step (drainCfg f .drain v ctx scratch core acc tail (a::xs)) =
      some (drainCfg f .drain (some (out a)) ctx (out a::scratch) core acc tail xs) := by
  have hout : (Turing.haltList f (a::xs)).stk f.k₁ = a::xs := by simp [Turing.haltList]
  change some (stepAux (program f inp out (.inr (.inl .drain))) (.inl v)
    (stackVals f (workStacks ctx scratch core acc tail) (Turing.haltList f (a::xs)).stk)) = _
  simp only [program,stepAux,stackVals,hout,List.head?_cons,Option.map_some,srcState,
    Option.isSome_some,Bool.cond_true,List.tail_cons,Option.getD_some]
  congr 1; congr 1
  rw [update_item,Shared.ComplexityBridge.TM2Compose.haltStacks_update,update_src,work_update_scratch]
  rfl

theorem drain_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx scratch core acc tail : List Bool) :
    (machine f inp out).step (drainCfg f .drain v ctx scratch core acc tail []) =
      some (drainCfg f .unload none ctx scratch core acc tail []) := by
  have hout : (Turing.haltList f []).stk f.k₁ = [] := by simp [Turing.haltList]
  change some (stepAux (program f inp out (.inr (.inl .drain))) (.inl v)
    (stackVals f (workStacks ctx scratch core acc tail) (Turing.haltList f []).stk)) = _
  simp only [program,stepAux,stackVals,hout,List.head?_nil,Option.map_none,srcState,
    Option.isSome_none,Bool.cond_false,List.tail_nil]
  congr 1; congr 1
  rw [update_item,Shared.ComplexityBridge.TM2Compose.haltStacks_update]

theorem unload_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx scratch core acc tail : List Bool) :
    (machine f inp out).step (drainCfg f .unload v ctx (b::scratch) core acc tail []) =
      some (drainCfg f .unload (some b) ctx scratch (b::core) acc tail []) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [update_src,work_update_scratch,update_src,work_update_core]
  rfl

theorem unload_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx core acc tail : List Bool) :
    (machine f inp out).step (drainCfg f .unload v ctx [] core acc tail []) =
      some (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) none ctx [] [] core acc tail)
        (Turing.haltList f []).stk) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [update_src,work_update_scratch]
  rfl

theorem drain_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (xs : List (f.Γ f.k₁)) (ctx scratch core acc tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (xs.length+1)
      (drainCfg f .drain v ctx scratch core acc tail xs) =
      some (drainCfg f .unload none ctx (xs.reverse.map out++scratch) core acc tail []) := by
  induction xs generalizing scratch v with
  | nil => exact drain_nil f inp out v ctx scratch core acc tail
  | cons a xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,drain_cons]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using ih (out a::scratch) (some (out a))

theorem unload_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (scratch ctx core acc tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (scratch.length+1)
      (drainCfg f .unload v ctx scratch core acc tail []) =
      some (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) none ctx [] []
        (scratch.reverse++core) acc tail) (Turing.haltList f []).stk) := by
  induction scratch generalizing core v with
  | nil => exact unload_nil f inp out v ctx core acc tail
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,unload_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::core) (some b)

/-- Copy an evaluator's halted output into the emitter's input in order. -/
theorem drain_item (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (bits ctx acc tail : List Bool) :
    runSteps (machine f inp out).step (2*bits.length+2)
      (itemEmbed f (workStacks ctx [] [] acc tail) (Turing.haltList f (bits.map out.symm))) =
      some (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) none ctx [] [] bits acc tail)
        (Turing.haltList f []).stk) := by
  have hd := drain_run f inp out (bits.map out.symm) ctx [] [] acc tail none
  have hbits : (bits.map out.symm).reverse.map out = bits.reverse := by simp [List.map_reverse,List.map_map]
  simp only [List.length_map,List.append_nil,hbits] at hd
  have hu := unload_run f inp out bits.reverse ctx [] acc tail none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hu
  rw [show 2*bits.length+2 = (bits.length+1)+(bits.length+1) by omega]
  change runSteps (machine f inp out).step ((bits.length+1)+(bits.length+1))
    (drainCfg f .drain none ctx [] [] acc tail (bits.map out.symm)) = _
  rw [runSteps_add,hd]
  exact hu


/-- Split a framed item and start the finite evaluator on the prepared pair.
The bound includes the splitter, dispatch, and both directions of the copy. -/
theorem split_load_item (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx bits acc tail : List Bool) :
    ∃ t ≤ 5*bits.length+2*ctx.length+6 + 2*(BitstringEncoding.delimit ctx++bits).length+3,
      runSteps (machine f inp out).step t
        (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc
          (BitstringEncoding.delimit bits++tail)) (Turing.initList f []).stk) =
      some (itemEmbed f (workStacks ctx [] [] acc tail)
        (Turing.initList f ((BitstringEncoding.delimit ctx++bits).map inp.symm))) := by
  let start := Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc
    (BitstringEncoding.delimit bits++tail)
  let finish := Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .ready) none ctx [] []
    (BitstringEncoding.delimit ctx++bits) acc tail
  have hs := Shared.ComplexityBridge.TM2ContextMapSplit.split_prepare ctx bits acc tail
  change runSteps S.step _ start = some finish at hs
  obtain ⟨d,hd,hr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    S.step (machine f inp out).step (fun q => srcEmbed f q (Turing.initList f []).stk)
    terminal stable (src_step f inp out (Turing.initList f []).stk) _ start finish (by rfl) hs
  let b := BitstringEncoding.delimit ctx++bits
  refine ⟨d+(2*b.length+3),by dsimp [b]; omega,?_⟩
  rw [runSteps_add,hr]
  exact load_item f inp out b ctx acc tail

/-- The whole split, evaluator and return segment is finite whenever the
item machine has the stated finite run and standard clean halt/output. -/
theorem split_call_item (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx bits output acc tail : List Bool) (n : Nat)
    (hf : runSteps f.step n (Turing.initList f ((BitstringEncoding.delimit ctx++bits).map inp.symm)) =
      some (Turing.haltList f (output.map out.symm))) :
    ∃ t ≤ 5*bits.length+2*ctx.length+6 + 2*(BitstringEncoding.delimit ctx++bits).length+3+n+2*output.length+2,
      runSteps (machine f inp out).step t
        (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc
          (BitstringEncoding.delimit bits++tail)) (Turing.initList f []).stk) =
      some (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) none ctx [] [] output acc tail)
        (Turing.haltList f []).stk) := by
  obtain ⟨d,hd,hs⟩ := split_load_item f inp out ctx bits acc tail
  have he := item_run f inp out (workStacks ctx [] [] acc tail) n _ _ hf
  have ho := drain_item f inp out output ctx acc tail
  refine ⟨d+n+(2*output.length+2),by omega,?_⟩
  rw [show d+n+(2*output.length+2) = d+(n+(2*output.length+2)) by omega,runSteps_add,hs]
  change runSteps (machine f inp out).step (n+(2*output.length+2)) _ = _
  rw [runSteps_add,he]
  exact ho


theorem emit_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (F : (k : f.K) → List (f.Γ k)) (v : Option Bool) (b : Bool) (ctx core acc tail : List Bool) :
    (machine f inp out).step
      (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) v ctx [] [] (b::core) acc tail) F) =
      some (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) (some b) ctx [] [] core (b::true::acc) tail) F) := by
  have hs := src_step f inp out F (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) v ctx [] [] (b::core) acc tail) (by intro h; cases h)
  have ht := Shared.ComplexityBridge.TM2ContextMapSplit.core_step
    (Shared.ComplexityBridge.TM2ContextMapBoundary.cfg .emit v ctx [] [] (b::core) acc) tail (by simp [Shared.ComplexityBridge.TM2ContextMapBoundary.cfg])
  change S.step (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) v ctx [] [] (b::core) acc tail) = _ at ht
  rw [Shared.ComplexityBridge.TM2ContextMapBoundary.emit_cons] at ht
  rw [ht] at hs
  exact hs

theorem emit_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (F : (k : f.K) → List (f.Γ k)) (v : Option Bool) (ctx acc tail : List Bool) :
    (machine f inp out).step
      (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) v ctx [] [] [] acc tail) F) =
      some (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .done) none ctx [] [] [] (false::acc) tail) F) := by
  have hs := src_step f inp out F (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) v ctx [] [] [] acc tail) (by intro h; cases h)
  have ht := Shared.ComplexityBridge.TM2ContextMapSplit.core_step
    (Shared.ComplexityBridge.TM2ContextMapBoundary.cfg .emit v ctx [] [] [] acc) tail (by simp [Shared.ComplexityBridge.TM2ContextMapBoundary.cfg])
  change S.step (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) v ctx [] [] [] acc tail) = _ at ht
  rw [Shared.ComplexityBridge.TM2ContextMapBoundary.emit_nil] at ht
  rw [ht] at hs
  exact hs

theorem emit_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (F : (k : f.K) → List (f.Γ k)) (output ctx acc tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (output.length+1)
      (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .emit) v ctx [] [] output acc tail) F) =
      some (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .done) none ctx [] [] []
        ((BitstringEncoding.delimit output).reverse++acc) tail) F) := by
  induction output generalizing acc v with
  | nil => simpa [runSteps,BitstringEncoding.delimit] using emit_nil f inp out F v ctx acc tail
  | cons b output ih =>
    rw [List.length_cons,show output.length+1+1 = (output.length+1)+1 by omega,runSteps_front,emit_cons]
    simpa [BitstringEncoding.delimit,List.reverse_cons,List.append_assoc] using ih (b::true::acc) (some b)

/-- One complete map-body segment, conditional only on the displayed finite
item run. The output is framed on the reverse accumulator and the tail is
unchanged; the returned state is the emitter's done label. -/
theorem split_call_emit (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx bits output acc tail : List Bool) (n : Nat)
    (hf : runSteps f.step n (Turing.initList f ((BitstringEncoding.delimit ctx++bits).map inp.symm)) =
      some (Turing.haltList f (output.map out.symm))) :
    ∃ t ≤ 5*bits.length+2*ctx.length+6 + 2*(BitstringEncoding.delimit ctx++bits).length+3+n+3*output.length+3,
      runSteps (machine f inp out).step t
        (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc
          (BitstringEncoding.delimit bits++tail)) (Turing.initList f []).stk) =
      some (srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .done) none ctx [] [] []
        ((BitstringEncoding.delimit output).reverse++acc) tail) (Turing.haltList f []).stk) := by
  obtain ⟨d,hd,hs⟩ := split_call_item f inp out ctx bits output acc tail n hf
  have he := emit_run f inp out (Turing.haltList f []).stk output ctx acc tail none
  refine ⟨d+(output.length+1),by omega,?_⟩
  rw [runSteps_add,hs]
  exact he


/-- The guarded-clause body has one finite item machine and a uniform clock
in the original formula request. The bound still includes all framing and
transfer operations of the enclosing machine. -/
theorem guard_item_segment :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (formula : Shared.ComplexityBridge.CNF.Formula)
        (clause : Shared.ComplexityBridge.CNF.Clause), clause ∈ formula → ∀ acc tail : List Bool,
      ∃ t ≤ 5*(BitstringEncoding.bitEncode clause).length + 2*(BitstringEncoding.bitEncode i).length + 6 +
          2*(BitstringEncoding.bitEncode (i,clause)).length + 3 +
          p.eval (BitstringEncoding.bitEncode (i,formula)).length +
          3*(BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.guardClause i clause)).length + 3,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (srcEmbed core.tm (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
            (BitstringEncoding.bitEncode i) [] [] [] acc
            (BitstringEncoding.delimit (BitstringEncoding.bitEncode clause)++tail))
            (Turing.initList core.tm []).stk) =
        some (srcEmbed core.tm (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .done) none
          (BitstringEncoding.bitEncode i) [] [] []
          ((BitstringEncoding.delimit (BitstringEncoding.bitEncode
            (Shared.ComplexityBridge.CNFDisjunction.guardClause i clause))).reverse++acc) tail)
          (Turing.haltList core.tm []).stk) := by
  obtain ⟨core,p,hp⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.guardFormula_item_run
  refine ⟨core,p,?_⟩
  intro i formula clause hclause acc tail
  obtain ⟨n,hn,hr⟩ := hp i formula clause hclause
  have hr' : runSteps core.tm.step n
      (Turing.initList core.tm ((BitstringEncoding.delimit (BitstringEncoding.bitEncode i) ++
        BitstringEncoding.bitEncode clause).map core.inputAlphabet.symm)) =
      some (Turing.haltList core.tm ((BitstringEncoding.bitEncode
        (Shared.ComplexityBridge.CNFDisjunction.guardClause i clause)).map core.outputAlphabet.symm)) := hr
  obtain ⟨t,ht,hs⟩ := split_call_emit core.tm core.inputAlphabet core.outputAlphabet
    (BitstringEncoding.bitEncode i) (BitstringEncoding.bitEncode clause)
    (BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.guardClause i clause)) acc tail n hr'
  refine ⟨t,?_,hs⟩
  change t ≤ 5*(BitstringEncoding.bitEncode clause).length + 2*(BitstringEncoding.bitEncode i).length + 6 +
    2*(BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode clause).length + 3 +
    p.eval (BitstringEncoding.bitEncode (i,formula)).length +
    3*(BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.guardClause i clause)).length+3
  omega

end Shared.ComplexityBridge.TM2ContextMapCall
