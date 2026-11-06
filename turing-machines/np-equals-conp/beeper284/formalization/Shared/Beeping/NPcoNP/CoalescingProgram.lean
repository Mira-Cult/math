import Shared.Beeping.NPcoNP.CoalescingActions

/-! Conditional lockstep register-program coalescing. The map, row
correspondence, and reachable ownership are parameters, not claims about the
284-state producer or the physical tape machine. -/

namespace Shared.Beeping.NPcoNP.CoalescingAlgebra
open PASoundness
open PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.MaskInvariant

def packConfig {n m states : Nat} (f : Fin n → Fin m)
    (c : Config n states) : Config m states := ⟨c.state, pack f c.bank⟩

def translateInstruction {n m states : Nat} (f : Fin n → Fin m)
    (i : MaskInvariant.Instruction n states) : MaskInvariant.Instruction m states :=
  ⟨translate f i.action, i.yes, i.no⟩

def RowsTranslate {n m states : Nat} (f : Fin n → Fin m)
    (source : MaskInvariant.Program n states) (target : MaskInvariant.Program m states) : Prop :=
  ∀ (s : Fin states), target.code[s] = translateInstruction f source.code[s]

private theorem outcome_step {n m states : Nat} (f : Fin n → Fin m)
    (a : Outcome m) (b : Outcome n) (yes no : Fin states)
    (h : a = ⟨pack f b.bank, b.success, b.output⟩) :
    ((⟨if a.success then yes else no, a.bank⟩ : Config m states), a.output) =
      (packConfig f (⟨if b.success then yes else no, b.bank⟩ : Config n states), b.output) := by
  cases b
  cases a
  cases h
  rfl

theorem step_commutes {n m states : Nat} (f : Fin n → Fin m)
    (source : MaskInvariant.Program n states) (target : MaskInvariant.Program m states)
    (hrows : RowsTranslate f source target) (c : Config n states)
    (howner : AccessOK f c.bank source.code[c.state].action) :
    target.system.step (packConfig f c) =
      (packConfig f (source.system.step c).1, (source.system.step c).2) := by
  have h := translate_execute f c.bank source.code[c.state].action howner
  simp only [MaskInvariant.Program.system, packConfig]
  rw [hrows c.state]
  simp only [translateInstruction]
  exact outcome_step f _ _ _ _ h

theorem run_pack {n m states : Nat} (f : Fin n → Fin m)
    (source : MaskInvariant.Program n states) (target : MaskInvariant.Program m states)
    (hstart : target.start = source.start) (hrows : RowsTranslate f source target)
    (howner : ∀ t, AccessOK f (source.system.run t).bank
      source.code[(source.system.run t).state].action) (t : Nat) :
    target.system.run t = packConfig f (source.system.run t) := by
  induction t with
  | zero =>
    simp only [WordEventSystem.run_zero]
    change (⟨target.start, fun _ => 0⟩ : Config m states) =
      ⟨source.start, pack f (fun _ => 0)⟩
    rw [hstart]
    congr 1
    funext j
    simp [pack]
  | succ t ih =>
    simp only [WordEventSystem.run_succ, ih]
    exact congrArg Prod.fst (step_commutes f source target hrows _ (howner t))

theorem prefixWord_eq {n m states : Nat} (f : Fin n → Fin m)
    (source : MaskInvariant.Program n states) (target : MaskInvariant.Program m states)
    (hstart : target.start = source.start) (hrows : RowsTranslate f source target)
    (howner : ∀ t, AccessOK f (source.system.run t).bank
      source.code[(source.system.run t).state].action) (t : Nat) :
    target.system.prefixWord t = source.system.prefixWord t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [WordEventSystem.prefix_succ, WordEventSystem.prefix_succ, ih,
      run_pack f source target hstart hrows howner t,
      step_commutes f source target hrows _ (howner t)]

end Shared.Beeping.NPcoNP.CoalescingAlgebra
