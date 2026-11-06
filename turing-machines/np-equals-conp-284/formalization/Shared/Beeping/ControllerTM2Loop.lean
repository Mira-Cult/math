import Shared.Beeping.ControllerCode
import Shared.Beeping.ControllerRefinement

/-! A finite-control TM2 loop around a comparison/update code. The program
runs on four finite-alphabet stacks. `startup` and `reject` are the only
beeping labels; the result tag is consumed by actual stack operations. -/
namespace Shared.Beeping.ControllerTM2Loop
open Turing Turing.PartrecToTM2 Turing.ToPartrec
open Shared.Beeping.ComparisonTM2 Shared.Beeping.ControllerCode
open Shared.ComplexityBridge.TM2Symbols
open TM2.Stmt

inductive Label
  | startup | running (q : Λ') | done | accept | reject
  deriving DecidableEq

instance : Inhabited Label := ⟨.startup⟩

abbrev Conf := TM2.Cfg (fun _ : K' => Γ') Label (Option Γ')
abbrev Statement := TM2.Stmt (fun _ : K' => Γ') Label (Option Γ')

/-- Replace a terminal instruction by a jump to the finite `done` label and
map all other jumps to their running counterparts. -/
def liftStmt : Stmt' → Statement
  | .push k f s => .push k f (liftStmt s)
  | .peek k f s => .peek k f (liftStmt s)
  | .pop k f s => .pop k f (liftStmt s)
  | .load f s => .load f (liftStmt s)
  | .branch f a b => .branch f (liftStmt a) (liftStmt b)
  | .goto f => .goto (fun v => .running (f v))
  | .halt => .goto (fun _ => .done)

def embed (c : Cfg') : Conf :=
  ⟨some (match c.l with | none => .done | some q => .running q),c.var,c.stk⟩

theorem liftAux (s : Stmt') (v : Option Γ') (st : ∀ _ : K', List Γ') :
    TM2.stepAux (liftStmt s) v st = embed (TM2.stepAux s v st) := by
  induction s generalizing v st with
  | push k f s ih => simpa [liftStmt,TM2.stepAux] using ih v (Function.update st k (f v :: st k))
  | peek k f s ih => simpa [liftStmt,TM2.stepAux] using ih (f v (st k).head?) st
  | pop k f s ih => simpa [liftStmt,TM2.stepAux] using ih (f v (st k).head?) (Function.update st k (st k).tail)
  | load f s ih => simpa [liftStmt,TM2.stepAux] using ih (f v) st
  | branch f a b iha ihb =>
    simp only [liftStmt,TM2.stepAux]
    cases h : f v <;> simp [h,iha,ihb]
  | goto f => rfl
  | halt => rfl

/-- The `done` block pops the leading Boolean number and its list separator.
The rest of the main stack is the next `[candidate,test]` input. -/
def program (c : Code) : Label → Statement
  | .startup => .push K'.main (fun _ => Γ'.cons) <|
      .push K'.main (fun _ => Γ'.cons) <|
      .load (fun _ => none) <| .goto (fun _ => .running (trNormal c Cont'.halt))
  | .running q => liftStmt (tr q)
  | .done => .pop K'.main (fun _ a => a) <|
      .branch (fun a => a = some Γ'.cons)
        (.load (fun _ => none) <| .goto (fun _ => .reject))
        (.pop K'.main (fun _ a => a) <|
          .load (fun _ => none) <| .goto (fun _ => .accept))
  | .accept => .goto (fun _ => .running (trNormal c Cont'.halt))
  | .reject => .goto (fun _ => .running (trNormal c Cont'.halt))

def initial : Conf := ⟨some .startup,none,K'.elim [] [] [] []⟩

def flag : Label → Bool
  | .startup | .reject => true
  | _ => false

def system (c : Code) : EventSystem Conf where
  initial := initial
  step x := ((TM2.step (program c) x).getD x, x.l.elim false flag)

theorem live_step (c : Code) (x y : Cfg') (h : TM2.step tr x = some y) :
    TM2.step (program c) (embed x) = some (embed y) := by
  cases x with
  | mk l v st =>
    cases l with
    | none => simp [TM2.step] at h
    | some q =>
      change some (TM2.stepAux (tr q) v st) = some y at h
      cases Option.some.inj h
      simp only [embed,program,TM2.step]
      rw [liftAux]
      rfl

theorem startup_step (c : Code) :
    TM2.step (program c) initial = some (embed (init c [0,0])) := by
  simp [TM2.step,TM2.stepAux,program,initial,embed,init,trList,trNat_zero,
    Function.update, K'.elim]

theorem done_step (c : Code) (b : Bool) (e n : Nat) :
    TM2.step (program c) (embed (halt [if b then 1 else 0,e,n])) =
      some ⟨some (if b then .accept else .reject),none,K'.elim (trList [e,n]) [] [] []⟩ := by
  cases b <;>
    simp [TM2.step,TM2.stepAux,program,embed,PartrecToTM2.halt,trList,trNat,trNum,trPosNum,
      Function.update,K'.elim]

theorem commit_step (c : Code) (b : Bool) (e n : Nat) :
    TM2.step (program c) ⟨some (if b then .accept else .reject),none,K'.elim (trList [e,n]) [] [] []⟩ =
      some (embed (init c [e,n])) := by
  cases b <;> simp [TM2.step,TM2.stepAux,program,embed,init]

/-- An executable finite support for the loop's control labels. -/
def support (c : Code) : Finset Label :=
  insert .startup (insert .done (insert .accept (insert .reject
    ((codeSupp c Cont'.halt).image Label.running))))

theorem lift_support (S : Finset Λ') (T : Finset Label)
    (hrun : ∀ q ∈ S, Label.running q ∈ T) (hdone : Label.done ∈ T)
    (s : Stmt') (hs : TM2.SupportsStmt S s) : TM2.SupportsStmt T (liftStmt s) := by
  induction s with
  | push k f s ih => exact ih hs
  | peek k f s ih => exact ih hs
  | pop k f s ih => exact ih hs
  | load f s ih => exact ih hs
  | branch f a b iha ihb => exact ⟨iha hs.1,ihb hs.2⟩
  | goto f => intro v; exact hrun (f v) (hs v)
  | halt => intro v; exact hdone

/-- All reachable program labels lie in an explicitly computed finite set. -/
theorem program_support (c : Code) : TM2.Supports (program c) (support c) := by
  have hstart : trNormal c Cont'.halt ∈ codeSupp c Cont'.halt :=
    codeSupp_self c Cont'.halt (trStmts₁_self _)
  have hrun : ∀ q ∈ codeSupp c Cont'.halt, Label.running q ∈ support c := by
    intro q hq
    simp [support,hq]
  have hdone : Label.done ∈ support c := by simp [support]
  constructor
  · change Label.startup ∈ support c
    simp [support]
  · intro q hq
    cases q with
    | startup => simpa [program,TM2.SupportsStmt] using hrun _ hstart
    | done =>
      simp [program,TM2.SupportsStmt,support]
    | accept => simpa [program,TM2.SupportsStmt] using hrun _ hstart
    | reject => simpa [program,TM2.SupportsStmt] using hrun _ hstart
    | running q =>
      have hq' : q ∈ codeSupp c Cont'.halt := by simpa [support] using hq
      exact lift_support _ _ hrun hdone _ ((tr_supports c Cont'.halt).2 q hq')

/-- Every program block produces a nonterminal label, including malformed
stack contents. -/
theorem program_step_live (c : Code) (q : Label) (v : Option Γ')
    (st : ∀ _ : K', List Γ') : (TM2.stepAux (program c q) v st).l ≠ none := by
  cases q with
  | startup => simp [program,TM2.stepAux]
  | running q => rw [program,liftAux]; simp [embed]
  | done =>
    simp only [program,TM2.stepAux]
    by_cases h : (st K'.main).head? = some Γ'.cons <;> simp [h]
  | accept => simp [program,TM2.stepAux]
  | reject => simp [program,TM2.stepAux]

theorem run_never_halts (c : Code) (t : Nat) : ((system c).run t).l ≠ none := by
  induction t with
  | zero => simp [system,initial]
  | succ t ih =>
    rw [EventSystem.run_succ]
    cases hcfg : (system c).run t with
    | mk l v st =>
      cases l with
      | none => simp [hcfg] at ih
      | some q =>
        change ((TM2.step (program c) ⟨some q,v,st⟩).getD ⟨some q,v,st⟩).l ≠ none
        simpa [TM2.step] using program_step_live c q v st

end Shared.Beeping.ControllerTM2Loop
