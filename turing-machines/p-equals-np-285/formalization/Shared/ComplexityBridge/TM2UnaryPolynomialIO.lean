import Shared.ComplexityBridge.TM2UnaryPolynomial
import Shared.ComplexityBridge.TM2ListCodec
import Shared.ComplexityBridge.TM2ComposeEncoded
import Shared.ComplexityBridge.BoundedHardness

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Canonical input/output boundaries for the fixed finite unary polynomial
machine. The input is read symbol by symbol and normalized to unary tokens;
all work stackVals are cleared before the result is returned. -/
namespace Shared.ComplexityBridge.TM2UnaryPolynomialIO
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Terms := Shared.Codes.NumericPolynomial.Terms
abbrev Poly := Shared.ComplexityBridge.TM2UnaryPolynomial.machine
abbrev PK := Shared.ComplexityBridge.TM2UnaryPolynomial.Key
abbrev Key := Unit ⊕ PK
inductive Phase where | load | clearA | clearB deriving DecidableEq
instance : Fintype Phase := Fintype.ofList [.load,.clearA,.clearB] (by intro l; cases l <;> simp)
abbrev Label (ts : Terms) := Phase ⊕ Shared.ComplexityBridge.TM2UnaryPolynomial.Label ts

def stackVals (input : List Bool) (S : PK → List Bool) : Key → List Bool
  | .inl _ => input | .inr k => S k

def embed (ts : Terms) (q : (Poly ts).Cfg) : Cfg (fun _ : Key => Bool) (Label ts) Bool :=
  ⟨q.l.map Sum.inr,q.var,stackVals [] q.stk⟩

def lift (ts : Terms) : (Poly ts).Stmt → Stmt (fun _ : Key => Bool) (Label ts) Bool
  | .push j h q => .push (.inr j) h (lift ts q)
  | .peek j h q => .peek (.inr j) h (lift ts q)
  | .pop j h q => .pop (.inr j) h (lift ts q)
  | .load h q => .load h (lift ts q)
  | .branch h q r => .branch h (lift ts q) (lift ts r)
  | .goto h => .goto (Sum.inr ∘ h)
  | .halt => .halt

theorem update_poly (input : List Bool) (S : PK → List Bool) (j : PK) (xs : List Bool) :
    Function.update (stackVals input S) (.inr j) xs = stackVals input (Function.update S j xs) := by
  funext k; cases k with
  | inl u => cases u; simp [stackVals,Function.update]
  | inr k =>
    by_cases h : k = j
    · subst k; simp [stackVals]
    · have hh : (Sum.inr k : Key) ≠ .inr j := by simpa using h
      simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]

theorem update_input (input : List Bool) (S : PK → List Bool) (xs : List Bool) :
    Function.update (stackVals input S) (.inl ()) xs = stackVals xs S := by
  funext k; cases k with
  | inl u => cases u; simp [stackVals,Function.update]
  | inr k => simp [stackVals,Function.update]

theorem lift_aux (ts : Terms) (q : (Poly ts).Stmt) (v : Bool) (S : PK → List Bool) :
    stepAux (lift ts q) v (stackVals [] S) = embed ts (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto h => rfl
  | load h q ih => exact ih _ _
  | peek j h q ih => exact ih _ _
  | push j h q ih => simp only [lift,stepAux]; rw [update_poly]; exact ih _ _
  | pop j h q ih => simp only [lift,stepAux]; rw [update_poly]; exact ih _ _
  | branch h q r ihq ihr => by_cases hh : h v <;> simp [lift,stepAux,hh,ihq,ihr]

def program (ts : Terms) : Label ts → Stmt (fun _ : Key => Bool) (Label ts) Bool
  | .inl .load => .pop (.inl ()) (fun _ h => h.isSome)
      (.branch id (.push (.inr (.inr .b)) (fun _ => true) (.goto (fun _ => .inl .load)))
        (.push (.inr (.inr .a)) (fun _ => true) (.goto (fun _ => .inr (Shared.ComplexityBridge.TM2UnaryPolynomial.startLabel ts)))))
  | .inl .clearA => .pop (.inr (.inr .a)) (fun _ h => h.isSome)
      (.branch id (.goto (fun _ => .inl .clearA)) (.goto (fun _ => .inl .clearB)))
  | .inl .clearB => .pop (.inr (.inr .b)) (fun _ h => h.isSome)
      (.branch id (.goto (fun _ => .inl .clearB)) (.load (fun _ => false) .halt))
  | .inr l => if l = Shared.ComplexityBridge.TM2UnaryPolynomial.doneLabel ts then
      .load (fun _ => false) (.goto (fun _ => .inl .clearA))
    else lift ts ((Poly ts).m l)

def machine (ts : Terms) : Turing.FinTM2 := by
  letI := Shared.ComplexityBridge.TM2UnaryPolynomial.labelFintype ts
  letI := Shared.ComplexityBridge.TM2UnaryPolynomial.labelDecidableEq ts
  exact {
    K := Key
    k₀ := .inl ()
    k₁ := .inr (.inl true)
    Γ := fun _ => Bool
    Λ := Label ts
    main := .inl .load
    σ := Bool
    initialState := false
    m := program ts }

theorem poly_step (ts : Terms) (q : (Poly ts).Cfg)
    (h : ¬Shared.ComplexityBridge.TM2UnaryPolynomial.doneTerminal ts q) :
    (machine ts).step (embed ts q) = ((Poly ts).step q).map (embed ts) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l =>
      have hl : l ≠ Shared.ComplexityBridge.TM2UnaryPolynomial.doneLabel ts := by intro he; apply h; exact congrArg some he
      change some (stepAux (program ts (.inr l)) v (stackVals [] S)) = _
      simp only [program,if_neg hl]
      rw [lift_aux]; rfl


def cfg (ts : Terms) (l : Phase) (flag : Bool) (input : List Bool) (n a out : Nat) : (machine ts).Cfg :=
  ⟨some (.inl l),flag,stackVals input (Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals n a out)⟩

theorem initial_eq (ts : Terms) (input : List Bool) : Turing.initList (machine ts) input = cfg ts .load false input 0 0 0 := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k with
  | inl u => cases u; simp [machine,cfg,stackVals,Turing.initList]
  | inr k => cases k with
    | inl b => cases b <;> simp [machine,cfg,stackVals,Turing.initList,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]
    | inr k => cases k <;> simp [machine,cfg,stackVals,Turing.initList,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]

theorem load_cons (ts : Terms) (flag b : Bool) (input : List Bool) (n : Nat) :
    (machine ts).step (cfg ts .load flag (b::input) n 0 0) = some (cfg ts .load true input (n+1) 0 0) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl u => cases u; simp [machine,cfg,stackVals,Function.update]
  | inr k => cases k with
    | inl z => cases z <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,List.replicate_succ]
    | inr j => cases j <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,List.replicate_succ]

theorem load_nil (ts : Terms) (flag : Bool) (n : Nat) :
    (machine ts).step (cfg ts .load flag [] n 0 0) =
      some (embed ts (Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg ts n 0)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl u => cases u; simp [machine,cfg,embed,stackVals,Function.update,Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg]
  | inr k => cases k with
    | inl z => cases z <;> simp [machine,cfg,embed,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
        Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]
    | inr j => cases j <;> simp [machine,cfg,embed,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
        Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]

theorem load_run (ts : Terms) (input : List Bool) (n : Nat) (flag : Bool) :
    runSteps (machine ts).step (input.length+1) (cfg ts .load flag input n 0 0) =
      some (embed ts (Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg ts (n+input.length) 0)) := by
  induction input generalizing n flag with
  | nil => simpa [runSteps] using load_nil ts flag n
  | cons b input ih =>
    rw [List.length_cons,show input.length+1+1 = (input.length+1)+1 by omega,runSteps_front,load_cons]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (n+1) true


theorem dispatch (ts : Terms) (n out : Nat) :
    (machine ts).step (embed ts (Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg ts n out)) =
      some (cfg ts .clearA false [] n 1 out) := by
  change some (Cfg.mk _ _ _) = _
  simp [machine,program,embed,cfg,Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg]

theorem clearA_cons (ts : Terms) (flag : Bool) (n a out : Nat) :
    (machine ts).step (cfg ts .clearA flag [] n (a+1) out) = some (cfg ts .clearA true [] n a out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl u => cases u; simp [machine,cfg,stackVals,Function.update]
  | inr k => cases k with
    | inl z => cases z <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,List.replicate_succ]
    | inr j => cases j <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,List.replicate_succ]

theorem clearA_nil (ts : Terms) (flag : Bool) (n out : Nat) :
    (machine ts).step (cfg ts .clearA flag [] n 0 out) = some (cfg ts .clearB false [] n 0 out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl u => cases u; simp [machine,cfg,stackVals,Function.update]
  | inr k => cases k with
    | inl z => cases z <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]
    | inr j => cases j <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]

theorem clearB_cons (ts : Terms) (flag : Bool) (n out : Nat) :
    (machine ts).step (cfg ts .clearB flag [] (n+1) 0 out) = some (cfg ts .clearB true [] n 0 out) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl u => cases u; simp [machine,cfg,stackVals,Function.update]
  | inr k => cases k with
    | inl z => cases z <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,List.replicate_succ]
    | inr j => cases j <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,List.replicate_succ]

theorem clearB_nil (ts : Terms) (flag : Bool) (out : Nat) :
    (machine ts).step (cfg ts .clearB flag [] 0 0 out) =
      some (Turing.haltList (machine ts) (List.replicate out true)) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k with
  | inl u => cases u; simp [machine,cfg,stackVals,Function.update,Turing.haltList]
  | inr k => cases k with
    | inl z => cases z <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,Turing.haltList,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]
    | inr j => cases j <;> simp [machine,cfg,stackVals,Function.update,Sum.inr.injEq,Turing.haltList,
        Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]

theorem clearA_run (ts : Terms) (n a out : Nat) (flag : Bool) :
    runSteps (machine ts).step (a+1) (cfg ts .clearA flag [] n a out) = some (cfg ts .clearB false [] n 0 out) := by
  induction a generalizing flag with
  | zero => exact clearA_nil ts flag n out
  | succ a ih =>
    rw [show a+1+1 = (a+1)+1 by omega,runSteps_front,clearA_cons]
    exact ih true

theorem clearB_run (ts : Terms) (n out : Nat) (flag : Bool) :
    runSteps (machine ts).step (n+1) (cfg ts .clearB flag [] n 0 out) =
      some (Turing.haltList (machine ts) (List.replicate out true)) := by
  induction n generalizing flag with
  | zero => exact clearB_nil ts flag out
  | succ n ih =>
    rw [show n+1+1 = (n+1)+1 by omega,runSteps_front,clearB_cons]
    exact ih true

theorem cleanup_run (ts : Terms) (n out : Nat) :
    runSteps (machine ts).step (n+4)
      (embed ts (Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg ts n out)) =
      some (Turing.haltList (machine ts) (List.replicate out true)) := by
  rw [show n+4 = 1+(2+(n+1)) by omega,Nat.add_comm 1 _,runSteps_front,dispatch]
  change runSteps (machine ts).step (2+(n+1)) (cfg ts .clearA false [] n 1 out) = _
  rw [runSteps_add]
  have h := clearA_run ts n 1 out false
  change runSteps (machine ts).step 2 (cfg ts .clearA false [] n 1 out) = _ at h
  rw [h]
  exact clearB_run ts n out false


/-- The full fixed-term unary evaluator consumes the actual raw input and
halts cleanly, charging loading, polynomial evaluation, and cleanup. -/
theorem raw_run (ts : Terms) (input : List Bool) :
    ∃ t ≤ Shared.ComplexityBridge.TM2UnaryPolynomial.cost ts input.length+2*input.length+5,
      runSteps (machine ts).step t (Turing.initList (machine ts) input) =
      some (Turing.haltList (machine ts) (List.replicate (Shared.Codes.NumericPolynomial.eval ts input.length) true)) := by
  obtain ⟨n,hn,hr⟩ := Shared.ComplexityBridge.TM2UnaryPolynomial.evaluate ts input.length 0
  let start := Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg ts input.length 0
  let finish := Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg ts input.length
    (Shared.Codes.NumericPolynomial.eval ts input.length)
  simp only [Nat.zero_add] at hr
  change runSteps (Poly ts).step n start = some finish at hr
  obtain ⟨d,hd,hs⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Poly ts).step (machine ts).step (embed ts) (Shared.ComplexityBridge.TM2UnaryPolynomial.doneTerminal ts)
    (Shared.ComplexityBridge.TM2UnaryPolynomial.done_stable ts) (poly_step ts) n start finish (by rfl) hr
  refine ⟨(input.length+1)+d+(input.length+4),by omega,?_⟩
  rw [initial_eq,show (input.length+1)+d+(input.length+4) =
    (input.length+1)+(d+(input.length+4)) by omega,runSteps_add]
  have hl := load_run ts input 0 false
  simp only [Nat.zero_add] at hl
  rw [hl]
  change runSteps (machine ts).step (d+(input.length+4)) (embed ts start) = _
  rw [runSteps_add,hs]
  exact cleanup_run ts input.length _

def unaryTerms (ts : Terms) (input : List Bool) : List Bool :=
  List.replicate (Shared.Codes.NumericPolynomial.eval ts input.length) true

noncomputable def rawTimeMachine (ts : Terms) : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (id : List Bool → List Bool) (unaryTerms ts) where
  tm := machine ts
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Shared.ComplexityBridge.TM2UnaryPolynomial.costPolynomial ts+Polynomial.C 2*Polynomial.X+Polynomial.C 5
  outputsFun input := by
    classical
    let t := Nat.find (raw_run ts input)
    have ht := (Nat.find_spec (raw_run ts input)).1
    have hr := (Nat.find_spec (raw_run ts input)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind (machine ts).step)^[t]
        (some (Turing.initList (machine ts) (input.map id))) =
        some (Turing.haltList (machine ts) ((unaryTerms ts input).map id))
      simpa [unaryTerms] using hr
    · change t ≤ (Shared.ComplexityBridge.TM2UnaryPolynomial.costPolynomial ts+Polynomial.C 2*Polynomial.X+Polynomial.C 5).eval input.length
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
        Shared.ComplexityBridge.TM2UnaryPolynomial.costPolynomial_eval]
      exact ht

def unaryPolynomial (p : Polynomial Nat) (input : List Bool) : List Bool :=
  List.replicate (p.eval input.length) true

/-- Every fixed natural polynomial has a finite canonical machine that
returns its value in unary, measured against the original raw bit length. -/
theorem unaryPolynomial_isPolyTime (p : Polynomial Nat) : ComplexityTheory.IsPolyTime (unaryPolynomial p) := by
  obtain ⟨ts,hts⟩ := Shared.Codes.NumericPolynomial.polynomial_represented p
  obtain ⟨first⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool) (id : List Bool → List Bool)
    (id : List Bool → List Bool) (unaryTerms ts)
    Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine (rawTimeMachine ts)
  obtain ⟨second⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (unaryTerms ts) (id : List Bool → List Bool) first Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine
  have he : unaryTerms ts = unaryPolynomial p := by
    funext input
    simp [unaryTerms,unaryPolynomial,hts]
  rw [he] at second
  exact ⟨second⟩

/-- The exact witness range length is generated in unary. -/
theorem witnessCount_isPolyTime (bound : Polynomial Nat) : ComplexityTheory.IsPolyTime
    (fun x : List Bool => List.replicate (bound.eval x.length+1) true) := by
  have h := unaryPolynomial_isPolyTime (bound+Polynomial.C 1)
  have he : unaryPolynomial (bound+Polynomial.C 1) = (fun x => List.replicate (bound.eval x.length+1) true) := by
    funext x
    simp [unaryPolynomial,Polynomial.eval_add,Polynomial.eval_C]
  rw [he] at h
  exact h

/-- The exact shared pair-input fuel is generated in unary, including the
full encoded public input and witness-length budget. -/
theorem commonFuel_isPolyTime (bound time : Polynomial Nat) : ComplexityTheory.IsPolyTime
    (fun x : List Bool => List.replicate (Shared.ComplexityBridge.BoundedHardness.commonFuel bound time x) true) := by
  let p : Polynomial Nat := time.comp (Polynomial.C 6*Polynomial.X+Polynomial.C 1+Polynomial.C 3*bound)
  have h := unaryPolynomial_isPolyTime p
  have he : unaryPolynomial p = (fun x => List.replicate (Shared.ComplexityBridge.BoundedHardness.commonFuel bound time x) true) := by
    funext x
    simp [unaryPolynomial,p,Shared.ComplexityBridge.BoundedHardness.commonFuel,
      Shared.ComplexityBridge.BoundedHardness.pairInputBound,Polynomial.eval_comp,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Nat.add_assoc]
  rw [he] at h
  exact h

namespace Fixtures
example : ∃ t ≤ 514,
    runSteps (machine [(3,2),(4,0)]).step t (Turing.initList (machine [(3,2),(4,0)]) [false,true]) =
      some (Turing.haltList (machine [(3,2),(4,0)]) (List.replicate 16 true)) := by
  have h := raw_run [(3,2),(4,0)] [false,true]
  norm_num [Shared.ComplexityBridge.TM2UnaryPolynomial.cost,Shared.Codes.NumericPolynomial.eval] at h ⊢
  exact h
example : unaryPolynomial 0 [] = [] := by simp [unaryPolynomial]
example : unaryPolynomial (Polynomial.X+Polynomial.C 1) [false,true] = [true,true,true] := by
  simp [unaryPolynomial]
end Fixtures

end Shared.ComplexityBridge.TM2UnaryPolynomialIO
