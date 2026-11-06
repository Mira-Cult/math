import Shared.ComplexityBridge.TM2FoldStateInstall
import Shared.ComplexityBridge.TM2ContextMapCall

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! A finite handoff around the existing split/evaluate/emit machine. The
returned state is framed in the reverse accumulator. This wrapper clears the
old state and consumes that framing to install the new state in order, then
returns to the next-item parser. The complete outer iteration and boundaries
are separate. -/
namespace Shared.ComplexityBridge.TM2FoldHandoff
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

abbrev Source (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :=
  Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out
abbrev Key (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.Key f
abbrev Alphabet (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.Alphabet f
abbrev State (f : Turing.FinTM2) := Shared.ComplexityBridge.TM2ContextMapCall.State f
inductive Phase where | clear | delimiter | bit | marker | reject deriving DecidableEq
instance : Fintype Phase := Fintype.ofList [.clear,.delimiter,.bit,.marker,.reject] (by intro l; cases l <;> simp)
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
  | .inl (.inl (.inl .done)) => .load (fun _ => .inl none) (.goto (fun _ => .inr .clear))
  | .inl l => lift f ((Source f inp out).m l)
  | .inr .clear => .pop (.inl (.inl .context)) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.goto (fun _ => .inr .clear)) (.goto (fun _ => .inr .delimiter)))
  | .inr .delimiter => .pop (.inl (.inl .accum)) (fun _ h => .inl h)
      (.branch (fun v => Shared.ComplexityBridge.TM2ContextMapCall.srcState f v == some false)
        (.goto (fun _ => .inr .bit)) (.goto (fun _ => .inr .reject)))
  | .inr .bit => .pop (.inl (.inl .accum)) (fun _ h => .inl h)
      (.branch (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).isSome)
        (.push (.inl (.inl .context)) (fun v => (Shared.ComplexityBridge.TM2ContextMapCall.srcState f v).getD false)
          (.goto (fun _ => .inr .marker)))
        (.load (fun _ => .inl none) (.goto (fun _ => .inl (.inl (.inr .header))))))
  | .inr .marker => .pop (.inl (.inl .accum)) (fun _ h => .inl h)
      (.branch (fun v => Shared.ComplexityBridge.TM2ContextMapCall.srcState f v == some true)
        (.goto (fun _ => .inr .bit)) (.goto (fun _ => .inr .reject)))
  | .inr .reject => .goto (fun _ => .inr .reject)

def machine (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) : Turing.FinTM2 := by
  letI := f.kFin; letI := f.ΛFin; letI := f.σFin
  exact {
    K := Key f
    k₀ := .inl (.inr ())
    k₁ := .inl (.inl .context)
    Γ := Alphabet f
    Λ := Label f
    main := .inl (.inl (.inr .header))
    σ := State f
    initialState := .inl none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := program f inp out }

def terminal (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Cfg) : Prop := q.l = some (.inl (.inl .done))
noncomputable instance (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :
    DecidablePred (terminal f inp out) := fun _ => Classical.propDecidable _

theorem stable (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Cfg) (h : terminal f inp out q) : (Source f inp out).step q = some q := by
  cases q with | mk l v st => change l = some (.inl (.inl .done)) at h; subst l; rfl

theorem core_step (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Source f inp out).Cfg) (h : ¬terminal f inp out q) :
    (machine f inp out).step (embed f inp out q) = ((Source f inp out).step q).map (embed f inp out) := by
  cases q with
  | mk l v st => cases l with
    | none => rfl
    | some l => cases l with
      | inl l => cases l with
        | inl l => cases l with
          | done => exact False.elim (h rfl)
          | scanPayload | restorePayload | scanContext | restoreContext | ready | emit =>
            change some (stepAux (lift f ((Source f inp out).m _)) v st) = _
            rw [lift_aux]; rfl
        | inr l => cases l <;>
            change some (stepAux (lift f ((Source f inp out).m _)) v st) = _ <;> rw [lift_aux] <;> rfl
      | inr l =>
        change some (stepAux (lift f ((Source f inp out).m _)) v st) = _
        rw [lift_aux]; rfl


def cfg (f : Turing.FinTM2) (l : Phase) (v : Option Bool) (ctx acc tail : List Bool) :
    Cfg (Alphabet f) (Label f) (State f) :=
  ⟨some (.inr l),.inl v,Shared.ComplexityBridge.TM2ContextMapCall.stackVals f
    (Shared.ComplexityBridge.TM2ContextMapCall.workStacks ctx [] [] acc tail) (Turing.haltList f []).stk⟩

theorem dispatch (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx acc tail : List Bool) :
    (machine f inp out).step (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .done) none ctx [] [] [] acc tail) (Turing.haltList f []).stk)) =
      some (cfg f .clear none ctx acc tail) := rfl

theorem clear_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx acc tail : List Bool) :
    (machine f inp out).step (cfg f .clear v (b::ctx) acc tail) = some (cfg f .clear (some b) ctx acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_context]
  rfl

theorem clear_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (acc tail : List Bool) :
    (machine f inp out).step (cfg f .clear v [] acc tail) = some (cfg f .delimiter none [] acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_context]
  rfl

theorem delimiter_false (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (acc tail : List Bool) :
    (machine f inp out).step (cfg f .delimiter v [] (false::acc) tail) = some (cfg f .bit (some false) [] acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_acc]
  rfl

theorem bit_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (ctx acc tail : List Bool) :
    (machine f inp out).step (cfg f .bit v ctx (b::acc) tail) = some (cfg f .marker (some b) (b::ctx) acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_acc,
    Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_context]
  rfl

theorem marker_true (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx acc tail : List Bool) :
    (machine f inp out).step (cfg f .marker v ctx (true::acc) tail) = some (cfg f .bit (some true) ctx acc tail) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_acc]
  rfl

theorem bit_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (ctx tail : List Bool) :
    (machine f inp out).step (cfg f .bit v ctx [] tail) =
      some (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] [] tail) (Turing.initList f []).stk)) := by
  have he : (Turing.haltList f []).stk = (Turing.initList f []).stk := by
    rw [Shared.ComplexityBridge.TM2Compose.haltStacks_empty,Shared.ComplexityBridge.TM2Compose.initStacks_empty]
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1
  rw [Shared.ComplexityBridge.TM2ContextMapCall.update_src,Shared.ComplexityBridge.TM2ContextMapIO.work_update_acc,he]
  rfl

theorem clear_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx acc tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (ctx.length+1) (cfg f .clear v ctx acc tail) =
      some (cfg f .delimiter none [] acc tail) := by
  induction ctx generalizing v with
  | nil => exact clear_nil f inp out v acc tail
  | cons b ctx ih =>
    rw [List.length_cons,show ctx.length+1+1 = (ctx.length+1)+1 by omega,runSteps_front,clear_cons]
    exact ih (some b)

def reverseBlocks (bits : List Bool) : List Bool := (bits.map (fun b => [b,true])).flatten

theorem bit_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (bits ctx tail : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (2*bits.length+1) (cfg f .bit v ctx (reverseBlocks bits) tail) =
      some (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (bits.reverse++ctx) [] [] [] [] tail)
        (Turing.initList f []).stk)) := by
  induction bits generalizing ctx v with
  | nil => exact bit_nil f inp out v ctx tail
  | cons b bits ih =>
    simp only [List.length_cons,reverseBlocks,List.map_cons,List.flatten_cons,List.cons_append]
    rw [show 2*(bits.length+1)+1 = ((2*bits.length+1)+1)+1 by omega,runSteps_front,bit_cons]
    change runSteps (machine f inp out).step ((2*bits.length+1)+1)
      (cfg f .marker (some b) (b::ctx) (true::reverseBlocks bits) tail) = _
    rw [runSteps_front,marker_true]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::ctx) (some true)

theorem reverse_delimit (bits : List Bool) :
    (BitstringEncoding.delimit bits).reverse = false::reverseBlocks bits.reverse := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [BitstringEncoding.delimit,List.reverse_cons,List.reverse_append,List.reverse_singleton,ih]
    simp [reverseBlocks,List.map_append,List.flatten_append,List.append_assoc]

/-- The emitted reverse framing is consumed and the exact returned state is
installed, with a charged restart and no change to the unread tail. -/
theorem handoff_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (old result tail : List Bool) :
    runSteps (machine f inp out).step (old.length+2*result.length+4)
      (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .done) none old [] [] []
          (BitstringEncoding.delimit result).reverse tail) (Turing.haltList f []).stk)) =
      some (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none result [] [] [] [] tail)
        (Turing.initList f []).stk)) := by
  have hc := clear_run f inp out old (BitstringEncoding.delimit result).reverse tail none
  have hb := bit_run f inp out result.reverse [] tail (some false)
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hb
  rw [show old.length+2*result.length+4 = 1+((old.length+1)+(1+(2*result.length+1))) by omega,
    Nat.add_comm 1 _,runSteps_front,dispatch]
  change runSteps (machine f inp out).step ((old.length+1)+(1+(2*result.length+1))) _ = _
  rw [runSteps_add,hc]
  change runSteps (machine f inp out).step (1+(2*result.length+1)) (cfg f .delimiter none [] (BitstringEncoding.delimit result).reverse tail) = _
  rw [reverse_delimit,Nat.add_comm 1 _,runSteps_front,delimiter_false]
  exact hb


/-- One complete outer step, including parsing, the finite evaluator, output
framing, state replacement, and return to the parser. The evaluator's finite
run is an explicit premise and its blocks are charged in the bound. -/
theorem step_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (old item result tail : List Bool) (n : Nat)
    (hf : runSteps f.step n (Turing.initList f ((BitstringEncoding.delimit old++item).map inp.symm)) =
      some (Turing.haltList f (result.map out.symm))) :
    ∃ t ≤ 5*item.length+3*old.length+2*(BitstringEncoding.delimit old++item).length+n+5*result.length+16,
      runSteps (machine f inp out).step t
        (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none old [] [] [] []
            (BitstringEncoding.delimit item++tail)) (Turing.initList f []).stk)) =
      some (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none result [] [] [] [] tail)
          (Turing.initList f []).stk)) := by
  obtain ⟨n',hn',hr⟩ := Shared.ComplexityBridge.TM2ContextMapCall.split_call_emit f inp out old item result [] tail n hf
  let start := Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none old [] [] [] []
      (BitstringEncoding.delimit item++tail)) (Turing.initList f []).stk
  let finish := Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .done) none old [] [] []
      (BitstringEncoding.delimit result).reverse tail) (Turing.haltList f []).stk
  have hrun : runSteps (Source f inp out).step n' start = some finish := by simpa [start,finish] using hr
  obtain ⟨d,hd,hs⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Source f inp out).step (machine f inp out).step (embed f inp out) (terminal f inp out)
    (stable f inp out) (core_step f inp out) n' start finish (by rfl) hrun
  refine ⟨d+(old.length+2*result.length+4),by omega,?_⟩
  rw [runSteps_add,hs]
  exact handoff_run f inp out old result tail


/-- The concrete indexed `guardAll` body, including its state handoff, has
one uniform polynomial clock in the whole original request at every pref. -/
theorem guard_step_prefix :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ P : Polynomial Nat,
      ∀ (i : Nat) (fs : List Shared.ComplexityBridge.CNF.Formula) (k : Nat)
        (f : Shared.ComplexityBridge.CNF.Formula), k ≤ fs.length → f ∈ fs → ∀ tail : List Bool,
      ∃ t ≤ P.eval (BitstringEncoding.bitEncode (i,fs)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (embed core.tm core.inputAlphabet core.outputAlphabet
            (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
              (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (i+k,Shared.ComplexityBridge.CNFDisjunction.guardAll i (fs.take k))) [] [] [] []
                (BitstringEncoding.delimit (BitstringEncoding.bitEncode f)++tail)) (Turing.initList core.tm []).stk)) =
        some (embed core.tm core.inputAlphabet core.outputAlphabet
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
              (BitstringEncoding.bitEncode (Shared.ComplexityBridge.TM2GuardAllStep.stateStep
                ((i+k,Shared.ComplexityBridge.CNFDisjunction.guardAll i (fs.take k)),f))) [] [] [] [] tail)
            (Turing.initList core.tm []).stk)) := by
  obtain ⟨core,p,hp⟩ := Shared.ComplexityBridge.TM2GuardAllStep.stateStep_prefix_run
  obtain ⟨q,hq⟩ := Shared.ComplexityBridge.TM2GuardAllStep.guardAll_prefix_size
  obtain ⟨r,hr⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.output_length_poly
    Shared.ComplexityBridge.TM2GuardAllStep.stateStep Shared.ComplexityBridge.TM2GuardAllStep.stateStep_isPolyTime
  let Q : Polynomial Nat := Polynomial.C 9*Polynomial.X+Polynomial.C 2*q+Polynomial.C 3
  let P : Polynomial Nat := Polynomial.C 35*Polynomial.X+Polynomial.C 7*q+p+Polynomial.C 5*(r.comp Q)+Polynomial.C 25
  refine ⟨core,P,?_⟩
  intro i fs k f hk hf tail
  let N := (BitstringEncoding.bitEncode (i,fs)).length
  let state := (i+k,Shared.ComplexityBridge.CNFDisjunction.guardAll i (fs.take k))
  let next := Shared.ComplexityBridge.TM2GuardAllStep.stateStep (state,f)
  have hcount : fs.length ≤ N := by
    have hh := Shared.ComplexityBridge.CNF.list_length_le_bitEncode fs
    change fs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]; omega
  have hi : (BitstringEncoding.bitEncode i).length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]; omega
  have hfsize : (BitstringEncoding.bitEncode f).length ≤ N := by
    have hh := Shared.ComplexityBridge.TM2MapSizeBounds.element_length_le hf
    change (BitstringEncoding.bitEncode f).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]; omega
  have hacc := hq i fs k
  have hidx := Shared.ComplexityBridge.TM2GuardAllStep.index_bits_add i k
  have hold : (BitstringEncoding.bitEncode state).length ≤ 4*N+q.eval N+1 := by
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (i+k))++
      BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.guardAll i (fs.take k))).length ≤ _
    simp only [List.length_append,BitstringEncoding.length_delimit]
    dsimp [N] at *; omega
  have hpair : (BitstringEncoding.bitEncode (state,f)).length ≤ Q.eval N := by
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode state)++BitstringEncoding.bitEncode f).length ≤ Q.eval N
    simp only [List.length_append,BitstringEncoding.length_delimit,Q,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  have hout : (BitstringEncoding.bitEncode next).length ≤ r.eval (Q.eval N) :=
    le_trans (hr (state,f)) (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono r hpair)
  obtain ⟨n,hn,hcore⟩ := hp i fs k f hk hf
  change runSteps core.tm.step n (Turing.initList core.tm ((BitstringEncoding.delimit (BitstringEncoding.bitEncode state)++
    BitstringEncoding.bitEncode f).map core.inputAlphabet.symm)) =
    some (Turing.haltList core.tm ((BitstringEncoding.bitEncode next).map core.outputAlphabet.symm)) at hcore
  obtain ⟨t,ht,hs⟩ := step_run core.tm core.inputAlphabet core.outputAlphabet
    (BitstringEncoding.bitEncode state) (BitstringEncoding.bitEncode f) (BitstringEncoding.bitEncode next) tail n hcore
  refine ⟨t,?_,hs⟩
  change t ≤ P.eval N
  simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_comp]
  change t ≤ 35*N+7*q.eval N+p.eval N+5*r.eval (Q.eval N)+25
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode state)++BitstringEncoding.bitEncode f).length ≤ Q.eval N at hpair
  simp only [Q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at hpair
  dsimp [N] at *
  omega


open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction

theorem guardAll_append (i : Nat) (xs ys : List Formula) :
    guardAll i (xs++ys) = guardAll i xs ++ guardAll (i+xs.length) ys := by
  induction xs generalizing i with
  | nil => simp [guardAll]
  | cons f xs ih =>
    simp [guardAll,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Iterating the concrete handoff across the entire encoded formula list
produces the canonical final `(index, accumulated formula)` state. The run
starts on explicit stacks; whole-input and clean-output boundaries remain. -/
theorem guardAll_loop :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (fs : List Formula),
      ∃ t ≤ p.eval (BitstringEncoding.bitEncode (i,fs)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (embed core.tm core.inputAlphabet core.outputAlphabet
            (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
              (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (i,([] : Formula))) [] [] [] [] (BitstringEncoding.bitEncode fs))
                (Turing.initList core.tm []).stk)) =
        some (embed core.tm core.inputAlphabet core.outputAlphabet
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
              (BitstringEncoding.bitEncode (i+fs.length,guardAll i fs)) [] [] [] [] [])
            (Turing.initList core.tm []).stk)) := by
  obtain ⟨core,q,hq⟩ := guard_step_prefix
  refine ⟨core,Polynomial.X*q,?_⟩
  intro i fs
  let N := (BitstringEncoding.bitEncode (i,fs)).length
  have hcount : fs.length ≤ N := by
    have hh := Shared.ComplexityBridge.CNF.list_length_le_bitEncode fs
    change fs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]; omega
  have walk : ∀ (suffix pref : List Formula), fs = pref++suffix →
      ∃ t ≤ suffix.length*q.eval N,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (embed core.tm core.inputAlphabet core.outputAlphabet
            (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
              (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (i+pref.length,guardAll i pref)) [] [] [] [] (BitstringEncoding.bitEncode suffix))
                (Turing.initList core.tm []).stk)) =
        some (embed core.tm core.inputAlphabet core.outputAlphabet
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
              (BitstringEncoding.bitEncode (i+fs.length,guardAll i fs)) [] [] [] [] [])
            (Turing.initList core.tm []).stk)) := by
    intro suffix
    induction suffix with
    | nil =>
      intro pref heq
      have hpref : fs = pref := by simpa using heq
      subst fs
      refine ⟨0,by simp,?_⟩
      have he : BitstringEncoding.bitEncode ([] : List Formula) = [] := rfl
      simp [runSteps,he]
    | cons f suffix ih =>
      intro pref heq
      have hk : pref.length ≤ fs.length := by rw [heq,List.length_append]; simp
      have hf : f ∈ fs := by rw [heq]; simp
      have htake : fs.take pref.length = pref := by rw [heq]; simp
      obtain ⟨t,ht,hs⟩ := hq i fs pref.length f hk hf (BitstringEncoding.bitEncode suffix)
      rw [htake] at hs
      have hnext : Shared.ComplexityBridge.TM2GuardAllStep.stateStep
          ((i+pref.length,guardAll i pref),f) =
          (i+(pref++[f]).length,guardAll i (pref++[f])) := by
        simp [Shared.ComplexityBridge.TM2GuardAllStep.stateStep,guardAll_append,guardAll,List.append_assoc,Nat.add_assoc]
      rw [hnext] at hs
      have heq' : fs = (pref++[f])++suffix := by simpa [List.append_assoc] using heq
      obtain ⟨u,hu,hr⟩ := ih (pref++[f]) heq'
      refine ⟨t+u,?_,?_⟩
      · change t ≤ q.eval N at ht
        rw [List.length_cons,Nat.succ_mul]; omega
      · rw [runSteps_add]
        change (runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (embed core.tm core.inputAlphabet core.outputAlphabet
            (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
              (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (i+pref.length,guardAll i pref)) [] [] [] []
                (BitstringEncoding.delimit (BitstringEncoding.bitEncode f)++BitstringEncoding.bitEncode suffix))
                (Turing.initList core.tm []).stk))).bind _ = _
        rw [hs]
        exact hr
  obtain ⟨t,ht,hr⟩ := walk fs [] (by simp)
  refine ⟨t,?_,?_⟩
  · change t ≤ (Polynomial.X*q).eval N
    simp only [Polynomial.eval_mul,Polynomial.eval_X]
    have hm := Nat.mul_le_mul_right (q.eval N) hcount
    omega
  · simpa [guardAll] using hr


theorem empty_done (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx : List Bool) :
    (machine f inp out).step
      (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] [] []) (Turing.initList f []).stk)) =
    some (embed f inp out (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none ctx [] [] [] [] []) (Turing.initList f []).stk)) := by
  let q := Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] [] []) (Turing.initList f []).stk
  have hs := core_step f inp out q (by intro h; cases h)
  have ht := Shared.ComplexityBridge.TM2ContextMapCall.src_step f inp out (Turing.initList f []).stk
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] [] []) (by intro h; cases h)
  rw [Shared.ComplexityBridge.TM2ContextMapSplit.header_nil] at ht
  rw [ht] at hs
  exact hs

/-- The entire traversal reaches the distinct empty-input done label, with
its final state serialized and the evaluator reset. -/
theorem guardAll_loop_done :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (fs : List Formula),
      ∃ t ≤ p.eval (BitstringEncoding.bitEncode (i,fs)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (embed core.tm core.inputAlphabet core.outputAlphabet
            (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
              (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (i,([] : Formula))) [] [] [] [] (BitstringEncoding.bitEncode fs))
              (Turing.initList core.tm []).stk)) =
        some (embed core.tm core.inputAlphabet core.outputAlphabet
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none
              (BitstringEncoding.bitEncode (i+fs.length,guardAll i fs)) [] [] [] [] [])
            (Turing.initList core.tm []).stk)) := by
  obtain ⟨core,p,hp⟩ := guardAll_loop
  refine ⟨core,p+Polynomial.C 1,?_⟩
  intro i fs
  obtain ⟨t,ht,hs⟩ := hp i fs
  refine ⟨t+1,?_,?_⟩
  · simp only [Polynomial.eval_add,Polynomial.eval_C]; omega
  · rw [runSteps_add,hs]
    exact empty_done core.tm core.inputAlphabet core.outputAlphabet _

namespace Fixtures
example : (BitstringEncoding.delimit [true,false]).reverse = [false,false,true,true,true] := by decide
end Fixtures

end Shared.ComplexityBridge.TM2FoldHandoff
