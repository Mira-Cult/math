import Shared.PNP.Record285.OwnershipExpandedEndpoint

/-! Verified deletion of unused registers by an injective renaming. The
relation covers every retained register and every omitted register, not just
the few values currently read by the graph. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.RegisterProjection
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore

def renameAction (f : Nat → Nat) : Action → Action
  | .inc i => .inc (f i)
  | .dec i => .dec (f i)
  | .half i => .half (f i)
  | .move src dst => .move (f src) (f dst)
  | .beep => .beep

def renameRow (f : Nat → Nat) (r : Row) : Row := ⟨renameAction f r.action,r.no,r.yes⟩

def BankRel (f : Nat → Nat) (old new : Nat → Nat) : Prop :=
  (∀ j, old (f j) = new j) ∧ (∀ k, (∀ j, f j ≠ k) → old k = 0)

theorem observe_rename (f : Nat → Nat) (a : Action) (old new : Nat → Nat)
    (h : BankRel f old new) : observe (renameAction f a) old = observe a new := by
  cases a <;> simp [renameAction,observe,h.1]

theorem update_retained (f : Nat → Nat) (hf : Function.Injective f) (a : Action)
    (old new : Nat → Nat) (h : BankRel f old new) (j : Nat) :
    update (renameAction f a) old (f j) = update a new j := by
  have heq (x y : Nat) : (f x = f y) ↔ x = y := ⟨fun hxy => hf hxy,fun hxy => congrArg f hxy⟩
  cases a <;> simp [renameAction,update,heq,h.1]

theorem update_omitted (f : Nat → Nat) (a : Action) (old : Nat → Nat) (k : Nat)
    (hk : ∀ j, f j ≠ k) : update (renameAction f a) old k = old k := by
  cases a <;> simp [renameAction,update,Ne.symm (hk _)]

theorem update_bankRel (f : Nat → Nat) (hf : Function.Injective f) (a : Action)
    (old new : Nat → Nat) (h : BankRel f old new) :
    BankRel f (update (renameAction f a) old) (update a new) := by
  refine ⟨fun j => update_retained f hf a old new h j,?_⟩
  intro k hk
  rw [update_omitted f a old k hk]
  exact h.2 k hk

theorem beep_rename (f : Nat → Nat) (a : Action) :
    decide (renameAction f a = .beep) = decide (a = .beep) := by
  cases a <;> rfl

def rowCheck (f : Nat → Nat) (original projected : Array Row) (i : Nat) : Bool :=
  match original[i]?, projected[i]? with
  | some old, some new => decide (old = renameRow f new ∧ new.no < projected.size ∧ new.yes < projected.size)
  | _, _ => false

def check (f : Nat → Nat) (original projected : Array Row) : Bool :=
  decide (original.size = projected.size ∧ 0 < projected.size) &&
    (List.range projected.size).all (rowCheck f original projected)

theorem checkRow_sound (f : Nat → Nat) (original projected : Array Row) (i : Nat)
    (row : Row) (hrow : projected[i]? = some row) (h : rowCheck f original projected i = true) :
    original[i]? = some (renameRow f row) ∧ row.no < projected.size ∧ row.yes < projected.size := by
  simp only [rowCheck,hrow] at h
  cases ho : original[i]? with
  | none => simp [ho] at h
  | some old =>
    have hc : old = renameRow f row ∧ row.no < projected.size ∧ row.yes < projected.size := by
      simpa [ho] using h
    obtain ⟨rfl,hn,hy⟩ := hc
    exact ⟨rfl,hn,hy⟩

def Rel (f : Nat → Nat) (projected : Array Row) (old new : State) : Prop :=
  old.index = new.index ∧ new.index < projected.size ∧ BankRel f old.bank new.bank

theorem initial_related (f : Nat → Nat) (original projected : Array Row)
    (h : check f original projected = true) : Rel f projected (system original).initial (system projected).initial := by
  simp only [check,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  exact ⟨rfl,h.1.2,⟨by intro j; rfl,by intro k hk; rfl⟩⟩

theorem step_related (f : Nat → Nat) (hf : Function.Injective f) (original projected : Array Row)
    (hcheck : check f original projected = true) (old new : State) (hrel : Rel f projected old new) :
    (step original old).2 = (step projected new).2 ∧
      Rel f projected (step original old).1 (step projected new).1 := by
  obtain ⟨hindex,hbound,hbank⟩ := hrel
  have hall : (List.range projected.size).all (rowCheck f original projected) = true := by
    simp only [check,Bool.and_eq_true_iff] at hcheck
    exact hcheck.2
  obtain ⟨row,hrow⟩ : ∃ row, projected[new.index]? = some row := ⟨projected[new.index],by simp⟩
  have hc := List.all_eq_true.mp hall new.index (List.mem_range.mpr hbound)
  obtain ⟨hold,hno,hyes⟩ := checkRow_sound f original projected new.index row hrow hc
  have hold' : original[old.index]? = some (renameRow f row) := by simpa [hindex] using hold
  have hbranch := observe_rename f row.action old.bank new.bank hbank
  let next := if observe row.action new.bank then row.yes else row.no
  have hn : next < projected.size := by
    dsimp [next]
    cases observe row.action new.bank <;> simp_all
  have hs : step original old =
      (⟨next,update (renameAction f row.action) old.bank⟩,decide (renameAction f row.action = .beep)) := by
    simp [step,hold',renameRow,hbranch,next]
  have hp : step projected new = (⟨next,update row.action new.bank⟩,decide (row.action = .beep)) := by
    simp [step,hrow,next]
  rw [hs,hp]
  exact ⟨beep_rename f row.action,rfl,hn,update_bankRel f hf row.action old.bank new.bank hbank⟩

/-- One source operation corresponds to exactly one projected operation. -/
noncomputable def simulation (f : Nat → Nat) (hf : Function.Injective f) (original projected : Array Row)
    (hcheck : check f original projected = true) : SegmentSimulation (system original) (system projected) where
  Rel := Rel f projected
  initial := initial_related f original projected hcheck
  duration := fun _ _ => 1
  positive := by intros; decide
  next := by
    intro old new h
    have hs := (step_related f hf original projected hcheck old new h).2
    simpa [system,EventSystem.advance] using hs
  event_iff := by
    intro old new h
    have hs := (step_related f hf original projected hcheck old new h).1
    change ((step original old).2 = true ↔ ∃ j, j < 1 ∧ (system projected).BeepFrom new j)
    constructor
    · intro he
      refine ⟨0,by decide,?_⟩
      simpa [EventSystem.BeepFrom,EventSystem.advance,system] using hs.symm.trans he
    · rintro ⟨j,hj,he⟩
      have hz : j = 0 := by omega
      subst j
      change (step projected new).2 = true at he
      exact hs.trans he
  event_unique := by
    intro old new h j k hj hk _ _
    omega

end Shared.PNP.Record285.RegisterProjection
