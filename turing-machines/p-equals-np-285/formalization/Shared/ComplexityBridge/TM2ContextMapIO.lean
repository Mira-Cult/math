import Shared.ComplexityBridge.TM2ContextMapLoop

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Canonical input and output boundaries for the context-map loop. The
loader separates a delimited context from the formula stream; the cleanup
removes context and reverses the accumulator into the designated output. -/
namespace Shared.ComplexityBridge.TM2ContextMapIO
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction

abbrev Source (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :=
  Shared.ComplexityBridge.TM2ContextMapLoop.machine f inp out
abbrev Key (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.Key f
abbrev Alphabet (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.Alphabet f
abbrev State (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.State f
inductive Phase where | header | data | restore | clear | output deriving DecidableEq
instance : Fintype Phase := Fintype.ofList [.header,.data,.restore,.clear,.output] (by intro l; cases l <;> simp)
abbrev Label (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.Label f ⊕ Phase

def embed (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) (q : (Source f inp out).Cfg) :
    Cfg (Alphabet f) (Label f) (State f) := ⟨q.l.map Sum.inl,q.var,q.stk⟩

def lift (f : Turing.FinTM2) : Stmt (Alphabet f) (Shared.ComplexityBridge.TM2ContextMapCall.Label f) (State f) →
    Stmt (Alphabet f) (Label f) (State f)
  | .push j h q => .push j h (lift f q)
  | .peek j h q => .peek j h (lift f q)
  | .pop j h q => .pop j h (lift f q)
  | .load h q => .load h (lift f q)
  | .branch h q r => .branch h (lift f q) (lift f r)
  | .goto h => .goto (Sum.inl ∘ h)
  | .halt => .halt

theorem lift_aux (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Stmt) (v : State f) (S : (k : Key f) → List (Alphabet f k)) :
    stepAux (lift f q) v S = embed f inp out (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto h => rfl
  | load h q ih => exact ih _ _
  | peek j h q ih => exact ih _ _
  | pop j h q ih => exact ih _ _
  | push j h q ih => exact ih _ _
  | branch h q r ihq ihr => by_cases hh : h v <;> simp [lift,stepAux,hh,ihq,ihr]

def program (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :
    Label f → Stmt (Alphabet f) (Label f) (State f)
  | .inl (.inl (.inr .done)) => .load (fun _ => .inl none) (.goto (fun _ => .inr .clear))
  | .inl l => lift f ((Source f inp out).m l)
  | .inr .header => .pop (.inl (.inr ())) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.branch (fun v => Shared.ComplexityBridge.TM2ContextMapCall.srcState f v == some true)
          (.goto (fun _ => .inr .data)) (.goto (fun _ => .inr .restore)))
        (.goto (fun _ => .inr .restore)))
  | .inr .data => .pop (.inl (.inr ())) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.push (.inl (.inl .scratch)) (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).getD false)
          (.goto (fun _ => .inr .header)))
        (.goto (fun _ => .inr .restore)))
  | .inr .restore => .pop (.inl (.inl .scratch)) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.push (.inl (.inl .context)) (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).getD false)
          (.goto (fun _ => .inr .restore)))
        (.load (fun _ => .inl none) (.goto (fun _ => .inl (.inl (.inr .header))))))
  | .inr .clear => .pop (.inl (.inl .context)) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.goto (fun _ => .inr .clear)) (.goto (fun _ => .inr .output)))
  | .inr .output => .pop (.inl (.inl .accum)) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.push (.inl (.inr ())) (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).getD false)
          (.goto (fun _ => .inr .output)))
        (.load (fun _ => .inl none) .halt))

def machine (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) : Turing.FinTM2 := by
  letI := f.kFin; letI := f.ΛFin; letI := f.σFin
  exact {
    K := Key f
    k₀ := .inl (.inr ())
    k₁ := .inl (.inr ())
    Γ := Alphabet f
    Λ := Label f
    main := .inr .header
    σ := State f
    initialState := .inl none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := program f inp out }

def terminal (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Cfg) : Prop := q.l = some (.inl (.inr .done))
noncomputable instance (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :
    DecidablePred (terminal f inp out) := fun _ => Classical.propDecidable _

theorem stable (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Cfg) (h : terminal f inp out q) : (Source f inp out).step q = some q := by
  cases q with
  | mk l v st => change l = some (.inl (.inr .done)) at h; subst l; rfl

theorem core_step (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Cfg) (h : ¬ terminal f inp out q) :
    (machine f inp out).step (embed f inp out q) = ((Source f inp out).step q).map (embed f inp out) := by
  cases q with
  | mk l v st => cases l with
    | none => rfl
    | some l =>
      cases l with
      | inl l => cases l with
        | inl l =>
          change some (stepAux (lift f ((Source f inp out).m _)) v st) = _
          rw [lift_aux]; rfl
        | inr l => cases l with
          | done => exact False.elim (h rfl)
          | header | data | restore | reject =>
            change some (stepAux (lift f ((Source f inp out).m _)) v st) = _
            rw [lift_aux]; rfl
      | inr l =>
        change some (stepAux (lift f ((Source f inp out).m _)) v st) = _
        rw [lift_aux]; rfl


abbrev Work := Shared.ComplexityBridge.TM2ContextMapCall.workStacks

theorem work_update_context (ctx scratch core acc tail xs : List Bool) :
    Function.update (Work ctx scratch core acc tail) (.inl .context) xs = Work xs scratch core acc tail := by
  funext k; cases k with
  | inl k => cases k <;> simp [Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
      Shared.ComplexityBridge.TM2ContextMapSplit.cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
      Shared.ComplexityBridge.TM2ContextMapSplit.cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem work_update_acc (ctx scratch core acc tail xs : List Bool) :
    Function.update (Work ctx scratch core acc tail) (.inl .accum) xs = Work ctx scratch core xs tail := by
  funext k; cases k with
  | inl k => cases k <;> simp [Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
      Shared.ComplexityBridge.TM2ContextMapSplit.cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update,Sum.inl.injEq]
  | inr k => cases k <;> simp [Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
      Shared.ComplexityBridge.TM2ContextMapSplit.cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

theorem work_update_tail (ctx scratch core acc tail xs : List Bool) :
    Function.update (Work ctx scratch core acc tail) (.inr ()) xs = Work ctx scratch core acc xs := by
  funext k; cases k with
  | inl k => cases k <;> simp [Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
      Shared.ComplexityBridge.TM2ContextMapSplit.cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,
      Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Function.update]
  | inr k => cases k <;> simp [Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
      Shared.ComplexityBridge.TM2ContextMapSplit.cfg,Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Function.update]

def cfg (f : Turing.FinTM2) (l : Phase) (v : Option Bool) (ctx scratch acc tail : List Bool) :
    Cfg (Alphabet f) (Label f) (State f) :=
  ⟨some (.inr l),.inl v,Shared.ComplexityBridge.TM2ContextMapCall.stackVals f
    (Work ctx scratch [] acc tail) (Turing.initList f []).stk⟩

theorem initial_eq (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) (bits : List Bool) :
    Turing.initList (machine f inp out) bits = cfg f .header none [] [] [] bits := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [machine,cfg,Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
        Shared.ComplexityBridge.TM2ContextMapCall.stackVals,Shared.ComplexityBridge.TM2ContextMapSplit.cfg,
        Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Turing.initList]
    | inr k => cases k <;> simp [machine,cfg,Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
        Shared.ComplexityBridge.TM2ContextMapCall.stackVals,Shared.ComplexityBridge.TM2ContextMapSplit.cfg,
        Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Turing.initList]
  | inr k =>
    rw [Shared.ComplexityBridge.TM2Compose.initStacks_empty]
    simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapCall.stackVals,Turing.initList]

theorem header_true (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx scratch acc tail : List Bool) :
    (machine f inp out).step (cfg f .header v ctx scratch acc (true::tail)) =
      some (cfg f .data (some true) ctx scratch acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_tail]
  rfl

theorem header_false (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx scratch acc tail : List Bool) :
    (machine f inp out).step (cfg f .header v ctx scratch acc (false::tail)) =
      some (cfg f .restore (some false) ctx scratch acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_tail]
  rfl

theorem data_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx scratch acc tail : List Bool) :
    (machine f inp out).step (cfg f .data v ctx scratch acc (b::tail)) =
      some (cfg f .header (some b) ctx (b::scratch) acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_tail,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch]
  rfl

theorem restore_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx scratch acc tail : List Bool) :
    (machine f inp out).step (cfg f .restore v ctx (b::scratch) acc tail) =
      some (cfg f .restore (some b) (b::ctx) scratch acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_context]
  rfl

theorem restore_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx acc tail : List Bool) :
    (machine f inp out).step (cfg f .restore v ctx [] acc tail) =
      some (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc tail) (Turing.initList f []).stk)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch]
  rfl

theorem scan_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (bits ctx scratch acc tail : List Bool) (v : Option Bool) :
    ∃ v', runSteps (machine f inp out).step (2*bits.length)
      (cfg f .header v ctx scratch acc (BitstringEncoding.delimit bits++tail)) =
      some (cfg f .header v' ctx (bits.reverse++scratch) acc (false::tail)) := by
  induction bits generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit]⟩
  | cons b bits ih =>
    obtain ⟨v',h⟩ := ih (b::scratch) (some b)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    rw [show 2*(bits.length+1) = (2*bits.length+1)+1 by omega,runSteps_front,header_true]
    change runSteps (machine f inp out).step (2*bits.length+1)
      (cfg f .data (some true) ctx scratch acc (b::(BitstringEncoding.delimit bits++tail))) = _
    rw [runSteps_front,data_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (scratch ctx acc tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (scratch.length+1) (cfg f .restore v ctx scratch acc tail) =
      some (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (scratch.reverse++ctx) [] [] [] acc tail)
        (Turing.initList f []).stk)) := by
  induction scratch generalizing ctx v with
  | nil => exact restore_nil f inp out v ctx acc tail
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::ctx) (some b)

/-- The canonical pair prefix is parsed and copied with no preloaded context. -/
theorem load_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx tail : List Bool) :
    runSteps (machine f inp out).step (3*ctx.length+2)
      (Turing.initList (machine f inp out) (BitstringEncoding.delimit ctx++tail)) =
      some (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] [] tail) (Turing.initList f []).stk)) := by
  obtain ⟨v,hs⟩ := scan_run f inp out ctx [] [] [] tail none
  simp only [List.append_nil] at hs
  have hr := restore_run f inp out ctx.reverse [] [] tail (some false)
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  rw [initial_eq,show 3*ctx.length+2 = 2*ctx.length+(1+(ctx.length+1)) by omega,runSteps_add,hs]
  change runSteps (machine f inp out).step (1+(ctx.length+1))
    (cfg f .header v [] ctx.reverse [] (false::tail)) = _
  rw [Nat.add_comm 1 _,runSteps_front,header_false]
  exact hr


theorem dispatch (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx acc : List Bool) :
    (machine f inp out).step (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none ctx [] [] [] acc []) (Turing.initList f []).stk)) =
      some (cfg f .clear none ctx [] acc []) := rfl

theorem clear_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx acc tail : List Bool) :
    (machine f inp out).step (cfg f .clear v (b::ctx) [] acc tail) =
      some (cfg f .clear (some b) ctx [] acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_context]
  rfl

theorem clear_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (acc tail : List Bool) :
    (machine f inp out).step (cfg f .clear v [] [] acc tail) =
      some (cfg f .output none [] [] acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_context]
  rfl

theorem output_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (acc tail : List Bool) :
    (machine f inp out).step (cfg f .output v [] [] (b::acc) tail) =
      some (cfg f .output (some b) [] [] acc (b::tail)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_acc,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_tail]
  rfl

theorem output_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (tail : List Bool) :
    (machine f inp out).step (cfg f .output v [] [] [] tail) =
      some (Turing.haltList (machine f inp out) tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,work_update_acc]
  funext k; cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [machine,cfg,Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
        Shared.ComplexityBridge.TM2ContextMapCall.stackVals,Shared.ComplexityBridge.TM2ContextMapSplit.cfg,
        Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Shared.ComplexityBridge.TM2ContextMapBoundary.stackVals,Turing.haltList]
    | inr k => cases k <;> simp [machine,cfg,Work,Shared.ComplexityBridge.TM2ContextMapCall.workStacks,
        Shared.ComplexityBridge.TM2ContextMapCall.stackVals,Shared.ComplexityBridge.TM2ContextMapSplit.cfg,
        Shared.ComplexityBridge.TM2ContextMapSplit.stackVals,Turing.haltList]
  | inr k =>
    rw [Shared.ComplexityBridge.TM2Compose.initStacks_empty]
    simp [machine,cfg,Shared.ComplexityBridge.TM2ContextMapCall.stackVals,Turing.haltList]

theorem clear_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx acc tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (ctx.length+1) (cfg f .clear v ctx [] acc tail) =
      some (cfg f .output none [] [] acc tail) := by
  induction ctx generalizing v with
  | nil => exact clear_nil f inp out v acc tail
  | cons b ctx ih =>
    rw [List.length_cons,show ctx.length+1+1 = (ctx.length+1)+1 by omega,runSteps_front,clear_cons]
    exact ih (some b)

theorem output_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (acc tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (acc.length+1) (cfg f .output v [] [] acc tail) =
      some (Turing.haltList (machine f inp out) (acc.reverse++tail)) := by
  induction acc generalizing tail v with
  | nil => exact output_nil f inp out v tail
  | cons b acc ih =>
    rw [List.length_cons,show acc.length+1+1 = (acc.length+1)+1 by omega,runSteps_front,output_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::tail) (some b)

theorem cleanup_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx acc : List Bool) :
    runSteps (machine f inp out).step (ctx.length+acc.length+3)
      (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none ctx [] [] [] acc []) (Turing.initList f []).stk)) =
      some (Turing.haltList (machine f inp out) acc.reverse) := by
  rw [show ctx.length+acc.length+3 = 1+((ctx.length+1)+(acc.length+1)) by omega,Nat.add_comm 1 _,
    runSteps_front,dispatch]
  change runSteps (machine f inp out).step ((ctx.length+1)+(acc.length+1)) (cfg f .clear none ctx [] acc []) = _
  rw [runSteps_add,clear_run]
  simpa using output_run f inp out acc [] none


/-- The complete finite TM2 reads the canonical pair and halts with the exact
canonical guarded formula. The stated polynomial charges loading, traversal,
context erasure, output reversal, and the standard halt boundary. -/
theorem guard_run :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (formula : Formula),
      ∃ t ≤ p.eval (BitstringEncoding.bitEncode (i,formula)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.bitEncode (i,formula))) =
        some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
          (BitstringEncoding.bitEncode (guardFormula i formula))) := by
  obtain ⟨core,p,hp⟩ := Shared.ComplexityBridge.TM2ContextMapLoop.guard_formula_done
  obtain ⟨q,hq⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.guardFormula_prefix_size
  let P : Polynomial Nat := p+q+Polynomial.C 4*Polynomial.X+Polynomial.C 5
  refine ⟨core,P,?_⟩
  intro i formula
  let ctx := BitstringEncoding.bitEncode i
  let tail := BitstringEncoding.bitEncode formula
  let result := BitstringEncoding.bitEncode (guardFormula i formula)
  let N := (BitstringEncoding.bitEncode (i,formula)).length
  obtain ⟨n,hn,hr⟩ := hp i formula
  let start := Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] [] tail) (Turing.initList core.tm []).stk
  let finish := Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none ctx [] [] [] result.reverse []) (Turing.initList core.tm []).stk
  change runSteps (Source core.tm core.inputAlphabet core.outputAlphabet).step n start = some finish at hr
  obtain ⟨d,hd,hs⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Source core.tm core.inputAlphabet core.outputAlphabet).step (machine core.tm core.inputAlphabet core.outputAlphabet).step
    (embed core.tm core.inputAlphabet core.outputAlphabet) (terminal core.tm core.inputAlphabet core.outputAlphabet)
    (stable core.tm core.inputAlphabet core.outputAlphabet) (core_step core.tm core.inputAlphabet core.outputAlphabet)
    n start finish (by rfl) hr
  have hctx : ctx.length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode formula).length
    simp only [List.length_append,BitstringEncoding.length_delimit]
    omega
  have hout : result.length ≤ q.eval N := by
    have hh := hq i formula formula.length
    simpa [result,N] using hh
  refine ⟨(3*ctx.length+2)+d+(ctx.length+result.length+3),?_,?_⟩
  · change (3*ctx.length+2)+d+(ctx.length+result.length+3) ≤ P.eval N
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    dsimp [N] at *
    omega
  · change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      ((3*ctx.length+2)+d+(ctx.length+result.length+3))
      (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.delimit ctx++tail)) = _
    rw [show (3*ctx.length+2)+d+(ctx.length+result.length+3) =
      (3*ctx.length+2)+(d+(ctx.length+result.length+3)) by omega,runSteps_add,load_run]
    change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      (d+(ctx.length+result.length+3)) (embed core.tm core.inputAlphabet core.outputAlphabet start) = _
    rw [runSteps_add,hs]
    have hc := cleanup_run core.tm core.inputAlphabet core.outputAlphabet ctx result.reverse
    simpa [finish,List.reverse_reverse,List.length_reverse] using hc

/-- The actual guarded-formula transformation is polynomial time in the
pinned canonical encodings, with a finite TM2 implementing the whole route. -/
theorem guardFormula_isPolyTime : ComplexityTheory.IsPolyTime
    (fun z : Nat × Formula => guardFormula z.1 z.2) := by
  obtain ⟨core,p,hp⟩ := guard_run
  refine ⟨{
    tm := machine core.tm core.inputAlphabet core.outputAlphabet
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p
    outputsFun := ?_ }⟩
  intro z
  rcases z with ⟨i,formula⟩
  classical
  let t := Nat.find (hp i formula)
  have ht := (Nat.find_spec (hp i formula)).1
  have hr := (Nat.find_spec (hp i formula)).2
  refine ⟨⟨t,?_⟩,ht⟩
  rw [runSteps_iterate] at hr
  change (fun o => o.bind (machine core.tm core.inputAlphabet core.outputAlphabet).step)^[t]
    (some (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (i,formula)).map id))) =
    some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (guardFormula i formula)).map id))
  simp only [List.map_id]
  exact hr


namespace Fixtures
example : runSteps (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)).step 2
    (Turing.initList (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)) [false]) =
    some (embed (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)
      (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed (Turing.idComputer Bool)
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none [] [] [] [] [] [])
        (Turing.initList (Turing.idComputer Bool) []).stk)) := by
  simpa [BitstringEncoding.delimit] using load_run (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool) [] []
example : runSteps (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)).step 3
    (embed (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)
      (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed (Turing.idComputer Bool)
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none [] [] [] [] [] [])
        (Turing.initList (Turing.idComputer Bool) []).stk)) =
    some (Turing.haltList (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)) []) := by
  simpa using cleanup_run (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool) [] []
end Fixtures

end Shared.ComplexityBridge.TM2ContextMapIO
