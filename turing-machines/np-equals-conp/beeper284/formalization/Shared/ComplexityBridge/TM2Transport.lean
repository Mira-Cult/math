import Shared.ComplexityBridge.TM2Boundary

namespace Shared.ComplexityBridge.TM2Symbols
open Turing.TM2

/-- Lift input and output lists through the alphabet equivalences. -/
def liftInputIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (input : List (tm.Γ tm.k₀)) :
    List ((normalizedIO tm).Γ (normalizedIO tm).k₀) := input.map (inputEquiv tm)

def liftOutputIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (output : List (tm.Γ tm.k₁)) :
    List ((normalizedIO tm).Γ (normalizedIO tm).k₁) := output.map (outputEquiv tm)

theorem erase_liftInputIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (input : List (tm.Γ tm.k₀)) :
    (liftInputIO tm input).map Subtype.val = input := by
  change (input.map (inputEquiv tm)).map Subtype.val = input
  induction input with
  | nil => rfl
  | cons a xs ih =>
    change a :: ((xs.map (inputEquiv tm)).map Subtype.val) = a :: xs
    rw [ih]

theorem erase_liftOutputIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (output : List (tm.Γ tm.k₁)) :
    (liftOutputIO tm output).map Subtype.val = output := by
  change (output.map (outputEquiv tm)).map Subtype.val = output
  induction output with
  | nil => rfl
  | cons a xs ih =>
    change a :: ((xs.map (outputEquiv tm)).map Subtype.val) = a :: xs
    rw [ih]

theorem cfg_ext {K Λ σ : Type} {Γ : K → Type} {c d : Cfg Γ Λ σ}
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c
  cases d
  cases hl
  cases hv
  cases hs
  rfl

theorem initList_input (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) :
    (Turing.initList tm input).stk tm.k₀ = input := by
  simp [Turing.initList]

theorem initList_other (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (k : tm.K) (h : k ≠ tm.k₀) : (Turing.initList tm input).stk k = [] := by
  simp [Turing.initList, h]

theorem haltList_output (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm output).stk tm.k₁ = output := by
  simp [Turing.haltList]

theorem haltList_other (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁))
    (k : tm.K) (h : k ≠ tm.k₁) : (Turing.haltList tm output).stk k = [] := by
  simp [Turing.haltList, h]

theorem initialIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (input : List (tm.Γ tm.k₀)) :
    eraseCfg (allowedIO tm) (Turing.initList (normalizedIO tm) (liftInputIO tm input)) =
      Turing.initList tm input := by
  let : DecidableEq tm.K := tm.kDecidableEq
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    change ((Turing.initList (normalizedIO tm) (liftInputIO tm input)).stk k).map Subtype.val =
      (Turing.initList tm input).stk k
    by_cases h : k = tm.k₀
    · subst k
      change ((Turing.initList (normalizedIO tm) (liftInputIO tm input)).stk (normalizedIO tm).k₀).map Subtype.val =
        (Turing.initList tm input).stk tm.k₀
      rw [initList_input (normalizedIO tm), initList_input tm]
      exact erase_liftInputIO tm input
    · rw [initList_other (normalizedIO tm) (liftInputIO tm input) k h, initList_other tm input k h]
      rfl

theorem haltIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (output : List (tm.Γ tm.k₁)) :
    eraseCfg (allowedIO tm) (Turing.haltList (normalizedIO tm) (liftOutputIO tm output)) =
      Turing.haltList tm output := by
  let : DecidableEq tm.K := tm.kDecidableEq
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    change ((Turing.haltList (normalizedIO tm) (liftOutputIO tm output)).stk k).map Subtype.val =
      (Turing.haltList tm output).stk k
    by_cases h : k = tm.k₁
    · subst k
      change ((Turing.haltList (normalizedIO tm) (liftOutputIO tm output)).stk (normalizedIO tm).k₁).map Subtype.val =
        (Turing.haltList tm output).stk tm.k₁
      rw [haltList_output (normalizedIO tm), haltList_output tm]
      exact erase_liftOutputIO tm output
    · rw [haltList_other (normalizedIO tm) (liftOutputIO tm output) k h, haltList_other tm output k h]
      rfl

/-- Exactly `n` TM2 transitions; further stepping after halt yields `none`. -/
def runSteps {α : Type} (step : α → Option α) : Nat → α → Option α
  | 0, c => some c
  | n + 1, c => (runSteps step n c).bind step

theorem runSteps_iterate {α : Type} (step : α → Option α) (n : Nat) (c : α) :
    runSteps step n c = (fun o => o.bind step)^[n] (some c) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [runSteps, Function.iterate_succ_apply', ih]

theorem runIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (n : Nat) (c : (normalizedIO tm).Cfg) :
    (runSteps (normalizedIO tm).step n c).map (eraseCfg (allowedIO tm)) =
      runSteps tm.step n (eraseCfg (allowedIO tm) c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runSteps, ← ih]
    cases h : runSteps (normalizedIO tm).step n c with
    | none => rfl
    | some d =>
      change ((normalizedIO tm).step d).map (eraseCfg (allowedIO tm)) =
        tm.step (eraseCfg (allowedIO tm) d)
      exact stepIO tm d

theorem runFromInputIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (n : Nat)
    (input : List (tm.Γ tm.k₀)) :
    (runSteps (normalizedIO tm).step n (Turing.initList (normalizedIO tm) (liftInputIO tm input))).map
        (eraseCfg (allowedIO tm)) = runSteps tm.step n (Turing.initList tm input) := by
  rw [← initialIO tm input]
  exact runIO tm n (Turing.initList (normalizedIO tm) (liftInputIO tm input))


theorem eraseCfg_injective {K Λ σ : Type} {Γ : K → Type} (A : ∀ k, Set (Γ k)) :
    Function.Injective (eraseCfg (Λ := Λ) (σ := σ) A) := by
  intro c d h
  apply cfg_ext
  · exact congrArg (fun x : Cfg Γ Λ σ => x.l) h
  · exact congrArg (fun x : Cfg Γ Λ σ => x.var) h
  · funext k
    have hs := congrFun (congrArg (fun x : Cfg Γ Λ σ => x.stk) h) k
    exact (Subtype.val_injective.list_map) hs


theorem runSteps_project {α β : Type} (f : α → Option α) (g : β → Option β)
    (project : β → α) (hstep : ∀ c, (g c).map project = f (project c))
    (n : Nat) (c : β) :
    (runSteps g n c).map project = runSteps f n (project c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runSteps, ← ih]
    cases h : runSteps g n c with
    | none => rfl
    | some d =>
      change (g d).map project = f (project d)
      exact hstep d

def transportEvalsToInTime {α β : Type} (f : α → Option α) (g : β → Option β)
    (project : β → α) (hstep : ∀ c, (g c).map project = f (project c))
    (hinj : Function.Injective project) (start finish : β) (bound : Nat)
    (h : StateTransition.EvalsToInTime f (project start) (some (project finish)) bound) :
    StateTransition.EvalsToInTime g start (some finish) bound := by
  have horig : runSteps f h.steps (project start) = some (project finish) := by
    rw [runSteps_iterate]
    exact h.evals_in_steps
  have hr := runSteps_project f g project hstep h.steps start
  rw [horig] at hr
  have hn : runSteps g h.steps start = some finish := by
    cases hs : runSteps g h.steps start with
    | none => simp [hs] at hr
    | some d =>
      have hd : project d = project finish := by simpa [hs] using hr
      have heq : d = finish := hinj hd
      simp [heq] at hs ⊢
  refine ⟨⟨h.steps, ?_⟩, h.steps_le_m⟩
  change (fun o : Option β => o.bind g)^[h.steps] (some start) = some finish
  rw [← runSteps_iterate]
  exact hn

noncomputable def outputsInTimeIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)]
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (bound : Nat)
    (h : Turing.TM2OutputsInTime tm input (some output) bound) :
    Turing.TM2OutputsInTime (normalizedIO tm) (liftInputIO tm input) (some (liftOutputIO tm output)) bound := by
  let start := Turing.initList (normalizedIO tm) (liftInputIO tm input)
  let finish := Turing.haltList (normalizedIO tm) (liftOutputIO tm output)
  have horig : StateTransition.EvalsToInTime tm.step
      (eraseCfg (allowedIO tm) start) (some (eraseCfg (allowedIO tm) finish)) bound := by
    dsimp only [start, finish]
    exact (initialIO tm input).symm ▸ (haltIO tm output).symm ▸ h
  exact transportEvalsToInTime tm.step (normalizedIO tm).step (eraseCfg (allowedIO tm))
    (stepIO tm) (eraseCfg_injective (allowedIO tm)) start finish bound horig


end Shared.ComplexityBridge.TM2Symbols
