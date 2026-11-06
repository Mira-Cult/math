import Shared.ComplexityBridge.TM2FoldHandoff

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Canonical input and clean output for the finite indexed formula fold.
The source loop operates on serialized `(index, accumulated formula)` states;
the loader constructs the initial `(index, [])` state from the actual input. -/
namespace Shared.ComplexityBridge.TM2FoldIO
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction
abbrev Source (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :=
  Shared.ComplexityBridge.TM2FoldHandoff.machine f inp out
abbrev Key (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.Key f
abbrev Alphabet (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.Alphabet f
abbrev State (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.State f
inductive Phase where | header | data | restore | scan | output | reject deriving DecidableEq
instance : Fintype Phase := Fintype.ofList [.header,.data,.restore,.scan,.output,.reject] (by intro l; cases l <;> simp)
abbrev Label (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2FoldHandoff.Label f ⊕ Phase

def embed (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) (q : (Source f inp out).Cfg) :
    Cfg (Alphabet f) (Label f) (State f) := ⟨q.l.map Sum.inl,q.var,q.stk⟩

def lift (f : Turing.FinTM2) : Stmt (Alphabet f) (Shared.ComplexityBridge.TM2FoldHandoff.Label f) (State f) →
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
  | .inl (.inl (.inl (.inr .done))) => .load (fun _ => .inl none) (.goto (fun _ => .inr .scan))
  | .inl l => lift f ((Source f inp out).m l)
  | .inr .header => .pop (.inl (.inr ())) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.branch (fun v => Shared.ComplexityBridge.TM2ContextMapCall.srcState f v == some true)
          (.push (.inl (.inl .scratch)) (fun _ => true) (.goto (fun _ => .inr .data)))
          (.push (.inl (.inl .scratch)) (fun _ => false) (.goto (fun _ => .inr .restore))))
        (.goto (fun _ => .inr .reject)))
  | .inr .data => .pop (.inl (.inr ())) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.push (.inl (.inl .scratch)) (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).getD false)
          (.goto (fun _ => .inr .header)))
        (.goto (fun _ => .inr .reject)))
  | .inr .restore => .pop (.inl (.inl .scratch)) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.push (.inl (.inl .context)) (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).getD false)
          (.goto (fun _ => .inr .restore)))
        (.load (fun _ => .inl none) (.goto (fun _ => .inl (.inl (.inl (.inr .header)))))))
  | .inr .scan => .pop (.inl (.inl .context)) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.push (.inl (.inl .scratch)) (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).getD false)
          (.goto (fun _ => .inr .scan))) (.goto (fun _ => .inr .output)))
  | .inr .output => .pop (.inl (.inl .scratch)) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.push (.inl (.inr ())) (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).getD false)
          (.goto (fun _ => .inr .output))) (.load (fun _ => .inl none) .halt))
  | .inr .reject => .goto (fun _ => .inr .reject)

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
    (q : (Source f inp out).Cfg) : Prop := q.l = some (.inl (.inl (.inr .done)))
noncomputable instance (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :
    DecidablePred (terminal f inp out) := fun _ => Classical.propDecidable _

theorem stable (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Cfg) (h : terminal f inp out q) : (Source f inp out).step q = some q := by
  cases q with | mk l v st => change l = some (.inl (.inl (.inr .done))) at h; subst l; rfl

theorem core_step (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Cfg) (h : ¬terminal f inp out q) :
    (machine f inp out).step (embed f inp out q) = ((Source f inp out).step q).map (embed f inp out) := by
  cases q with
  | mk l v st => cases l with
    | none => rfl
    | some l => cases l with
      | inl l => cases l with
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
      | inr l =>
        change some (stepAux (lift f ((Source f inp out).m _)) v st) = _
        rw [lift_aux]; rfl


abbrev Work := Shared.ComplexityBridge.TM2ContextMapCall.workStacks
open Shared.ComplexityBridge.CNFLiteralConstructor (framedBits delimit_prefix)

def cfg (f : Turing.FinTM2) (l : Phase) (v : Option Bool) (ctx scratch tail : List Bool) :
    Cfg (Alphabet f) (Label f) (State f) :=
  ⟨some (.inr l),.inl v,Shared.ComplexityBridge.TM2ContextMapCall.stackVals f
    (Work ctx scratch [] [] tail) (Turing.initList f []).stk⟩

theorem initial_eq (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) (bits : List Bool) :
    Turing.initList (machine f inp out) bits = cfg f .header none [] [] bits := by
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
    (v : Option Bool) (ctx scratch tail : List Bool) :
    (machine f inp out).step (cfg f .header v ctx scratch (true::tail)) =
      some (cfg f .data (some true) ctx (true::scratch) tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_tail,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch]
  rfl

theorem header_false (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx scratch tail : List Bool) :
    (machine f inp out).step (cfg f .header v ctx scratch (false::tail)) =
      some (cfg f .restore (some false) ctx (false::scratch) tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_tail,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch]
  rfl

theorem data_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx scratch tail : List Bool) :
    (machine f inp out).step (cfg f .data v ctx scratch (b::tail)) =
      some (cfg f .header (some b) ctx (b::scratch) tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_tail,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch]
  rfl

theorem restore_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx scratch tail : List Bool) :
    (machine f inp out).step (cfg f .restore v ctx (b::scratch) tail) =
      some (cfg f .restore (some b) (b::ctx) scratch tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_context]
  rfl

theorem restore_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx tail : List Bool) :
    (machine f inp out).step (cfg f .restore v ctx [] tail) =
      some (embed f inp out (Shared.ComplexityBridge.TM2FoldHandoff.embed f inp out
        (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] [] tail) (Turing.initList f []).stk))) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch]
  rfl

theorem header_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (bits ctx scratch tail : List Bool) (v : Option Bool) :
    ∃ v', runSteps (machine f inp out).step (2*bits.length)
      (cfg f .header v ctx scratch (BitstringEncoding.delimit bits++tail)) =
      some (cfg f .header v' ctx ((framedBits bits).reverse++scratch) (false::tail)) := by
  induction bits generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit,framedBits]⟩
  | cons b bits ih =>
    obtain ⟨v',h⟩ := ih (b::true::scratch) (some b)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    rw [show 2*(bits.length+1) = (2*bits.length+1)+1 by omega,runSteps_front,header_true]
    change runSteps (machine f inp out).step (2*bits.length+1)
      (cfg f .data (some true) ctx (true::scratch) (b::(BitstringEncoding.delimit bits++tail))) = _
    rw [runSteps_front,data_cons]
    simpa [framedBits,List.reverse_cons,List.append_assoc] using h

theorem restore_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (scratch ctx tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (scratch.length+1) (cfg f .restore v ctx scratch tail) =
      some (embed f inp out (Shared.ComplexityBridge.TM2FoldHandoff.embed f inp out
        (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (scratch.reverse++ctx) [] [] [] [] tail)
          (Turing.initList f []).stk))) := by
  induction scratch generalizing ctx v with
  | nil => exact restore_nil f inp out v ctx tail
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::ctx) (some b)

/-- Copy the input's first delimited component as a complete block into the
initial state stack. The remaining encoded formula list stays in place. -/
theorem load_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (bits tail : List Bool) :
    runSteps (machine f inp out).step (4*bits.length+3)
      (Turing.initList (machine f inp out) (BitstringEncoding.delimit bits++tail)) =
      some (embed f inp out (Shared.ComplexityBridge.TM2FoldHandoff.embed f inp out
        (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.delimit bits) [] [] [] [] tail)
          (Turing.initList f []).stk))) := by
  obtain ⟨v,hs⟩ := header_run f inp out bits [] [] tail none
  simp only [List.append_nil] at hs
  have hr := restore_run f inp out (false::(framedBits bits).reverse) [] tail (some false)
  simp only [List.reverse_cons,List.reverse_reverse,List.append_nil,List.length_cons,List.length_reverse,
    Shared.ComplexityBridge.CNFLiteralConstructor.prefix_length] at hr
  have he : (framedBits bits ++ [false]) = BitstringEncoding.delimit bits := (delimit_prefix bits).symm
  rw [he] at hr
  rw [initial_eq,show 4*bits.length+3 = 2*bits.length+(1+(2*bits.length+2)) by omega,runSteps_add,hs]
  change runSteps (machine f inp out).step (1+(2*bits.length+2))
    (cfg f .header v [] (framedBits bits).reverse (false::tail)) = _
  rw [Nat.add_comm 1 _,runSteps_front,header_false]
  exact hr


theorem dispatch (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx : List Bool) :
    (machine f inp out).step (embed f inp out (Shared.ComplexityBridge.TM2FoldHandoff.embed f inp out
      (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none ctx [] [] [] [] []) (Turing.initList f []).stk))) =
      some (cfg f .scan none ctx [] []) := rfl

theorem scan_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx scratch tail : List Bool) :
    (machine f inp out).step (cfg f .scan v (b::ctx) scratch tail) =
      some (cfg f .scan (some b) ctx (b::scratch) tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_context,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch]
  rfl

theorem scan_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (scratch tail : List Bool) :
    (machine f inp out).step (cfg f .scan v [] scratch tail) = some (cfg f .output none [] scratch tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_context]
  rfl

theorem output_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (scratch tail : List Bool) :
    (machine f inp out).step (cfg f .output v [] (b::scratch) tail) =
      some (cfg f .output (some b) [] scratch (b::tail)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_tail]
  rfl

theorem output_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (tail : List Bool) :
    (machine f inp out).step (cfg f .output v [] [] tail) =
      some (Turing.haltList (machine f inp out) tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapCall.work_update_scratch]
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

theorem scan_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx scratch tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (ctx.length+1) (cfg f .scan v ctx scratch tail) =
      some (cfg f .output none [] (ctx.reverse++scratch) tail) := by
  induction ctx generalizing scratch v with
  | nil => exact scan_nil f inp out v scratch tail
  | cons b ctx ih =>
    rw [List.length_cons,show ctx.length+1+1 = (ctx.length+1)+1 by omega,runSteps_front,scan_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::scratch) (some b)

theorem output_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (scratch tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (scratch.length+1) (cfg f .output v [] scratch tail) =
      some (Turing.haltList (machine f inp out) (scratch.reverse++tail)) := by
  induction scratch generalizing tail v with
  | nil => exact output_nil f inp out v tail
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,output_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::tail) (some b)

/-- The final serialized state is moved to the output in order, with all
other stacks cleared and the standard halt state restored. -/
theorem cleanup_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx : List Bool) :
    runSteps (machine f inp out).step (2*ctx.length+3)
      (embed f inp out (Shared.ComplexityBridge.TM2FoldHandoff.embed f inp out
        (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none ctx [] [] [] [] []) (Turing.initList f []).stk))) =
      some (Turing.haltList (machine f inp out) ctx) := by
  have hs := scan_run f inp out ctx [] [] none
  simp only [List.append_nil] at hs
  have ho := output_run f inp out ctx.reverse [] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at ho
  rw [show 2*ctx.length+3 = 1+((ctx.length+1)+(ctx.length+1)) by omega,Nat.add_comm 1 _,runSteps_front,dispatch]
  change runSteps (machine f inp out).step ((ctx.length+1)+(ctx.length+1)) (cfg f .scan none ctx [] []) = _
  rw [runSteps_add,hs]
  exact ho


def foldResult (p : Nat × List Formula) : Nat × Formula :=
  (p.1+p.2.length,guardAll p.1 p.2)

/-- Complete finite TM2 run on the canonical request, with the final fold
state in the standard output stack and all other stacks empty. -/
theorem fold_run :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ P : Polynomial Nat,
      ∀ (i : Nat) (fs : List Formula),
      ∃ t ≤ P.eval (BitstringEncoding.bitEncode (i,fs)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.bitEncode (i,fs))) =
        some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
          (BitstringEncoding.bitEncode (foldResult (i,fs)))) := by
  obtain ⟨core,p,hp⟩ := Shared.ComplexityBridge.TM2FoldHandoff.guardAll_loop_done
  obtain ⟨q,hq⟩ := Shared.ComplexityBridge.TM2GuardAllStep.guardAll_prefix_size
  let P : Polynomial Nat := p+Polynomial.C 2*q+Polynomial.C 12*Polynomial.X+Polynomial.C 8
  refine ⟨core,P,?_⟩
  intro i fs
  let bits := BitstringEncoding.bitEncode i
  let tail := BitstringEncoding.bitEncode fs
  let result := BitstringEncoding.bitEncode (foldResult (i,fs))
  let N := (BitstringEncoding.bitEncode (i,fs)).length
  obtain ⟨n,hn,hr⟩ := hp i fs
  let start := Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
    (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.delimit bits) [] [] [] [] tail)
      (Turing.initList core.tm []).stk)
  let finish := Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
    (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none result [] [] [] [] [])
      (Turing.initList core.tm []).stk)
  have he : BitstringEncoding.bitEncode (i,([] : Formula)) = BitstringEncoding.delimit (BitstringEncoding.bitEncode i) := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode i) ++ [] = _
    simp
  rw [he] at hr
  change runSteps (Source core.tm core.inputAlphabet core.outputAlphabet).step n start = some finish at hr
  obtain ⟨d,hd,hs⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Source core.tm core.inputAlphabet core.outputAlphabet).step (machine core.tm core.inputAlphabet core.outputAlphabet).step
    (embed core.tm core.inputAlphabet core.outputAlphabet) (terminal core.tm core.inputAlphabet core.outputAlphabet)
    (stable core.tm core.inputAlphabet core.outputAlphabet) (core_step core.tm core.inputAlphabet core.outputAlphabet)
    n start finish (by rfl) hr
  have hcount : fs.length ≤ N := by
    have hh := Shared.ComplexityBridge.CNF.list_length_le_bitEncode fs
    change fs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]; omega
  have hbits : bits.length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]; omega
  have hidx := Shared.ComplexityBridge.TM2GuardAllStep.index_bits_add i fs.length
  have hguard : (BitstringEncoding.bitEncode (guardAll i fs)).length ≤ q.eval N := by
    have hh := hq i fs fs.length
    simpa [N] using hh
  have hresult : result.length ≤ 4*N+q.eval N+1 := by
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (i+fs.length))++
      BitstringEncoding.bitEncode (guardAll i fs)).length ≤ _
    simp only [List.length_append,BitstringEncoding.length_delimit]
    dsimp [bits,N] at *
    omega
  refine ⟨(4*bits.length+3)+d+(2*result.length+3),?_,?_⟩
  · change (4*bits.length+3)+d+(2*result.length+3) ≤ P.eval N
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    dsimp [N] at *
    omega
  · change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      ((4*bits.length+3)+d+(2*result.length+3))
      (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.delimit bits++tail)) = _
    rw [show (4*bits.length+3)+d+(2*result.length+3) =
      (4*bits.length+3)+(d+(2*result.length+3)) by omega,runSteps_add,load_run]
    change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      (d+(2*result.length+3)) (embed core.tm core.inputAlphabet core.outputAlphabet start) = _
    rw [runSteps_add,hs]
    exact cleanup_run core.tm core.inputAlphabet core.outputAlphabet result

theorem foldResult_isPolyTime : ComplexityTheory.IsPolyTime foldResult := by
  obtain ⟨core,p,hp⟩ := fold_run
  refine ⟨{
    tm := machine core.tm core.inputAlphabet core.outputAlphabet
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p
    outputsFun := ?_ }⟩
  intro z
  rcases z with ⟨i,fs⟩
  classical
  let t := Nat.find (hp i fs)
  have ht := (Nat.find_spec (hp i fs)).1
  have hr := (Nat.find_spec (hp i fs)).2
  refine ⟨⟨t,?_⟩,ht⟩
  rw [runSteps_iterate] at hr
  change (fun o => o.bind (machine core.tm core.inputAlphabet core.outputAlphabet).step)^[t]
    (some (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (i,fs)).map id))) =
    some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (foldResult (i,fs))).map id))
  simp only [List.map_id]
  exact hr

/-- The actual `guardAll` function is polynomial time in the pinned Google
encoding. Input loading, repeated index updates, and output projection all
have finite machine witnesses and charged polynomial bounds. -/
theorem guardAll_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × List Formula => guardAll p.1 p.2) := by
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp foldResult
    (fun p : Nat × Formula => p.2) foldResult_isPolyTime Shared.ComplexityBridge.TM2GuardAllStep.second_isPolyTime
  simpa [foldResult] using h

end Shared.ComplexityBridge.TM2FoldIO
