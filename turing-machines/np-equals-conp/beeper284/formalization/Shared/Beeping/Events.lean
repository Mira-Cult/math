import Std

/-!
Deterministic transition-labelled systems. `step` is total and returns the
configuration after the transition together with its beep flag. Transition
number `t` starts at configuration `t`; initial occupancy is not an event.
-/
namespace Shared.Beeping

structure EventSystem (Config : Type) where
  initial : Config
  step : Config → Config × Bool

namespace EventSystem

variable {Config : Type} (M : EventSystem Config)

def run : Nat → Config
  | 0 => M.initial
  | t + 1 => (M.step (run t)).1

def BeepAt (t : Nat) : Prop := (M.step (M.run t)).2 = true

def EventuallySilent : Prop := ∃ T, ∀ t, T ≤ t → ¬ M.BeepAt t

/-- A finite set of event times, expressed as an exhaustive finite list. -/
def FiniteEventTimes : Prop := ∃ times : List Nat, ∀ t, M.BeepAt t → t ∈ times

@[simp] theorem run_zero : M.run 0 = M.initial := rfl
@[simp] theorem run_succ (t : Nat) : M.run (t + 1) = (M.step (M.run t)).1 := rfl

theorem eventuallySilent_iff_finiteEventTimes :
    M.EventuallySilent ↔ M.FiniteEventTimes := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨List.range T, ?_⟩
    intro t ht
    have hlt : t < T := Nat.lt_of_not_ge (fun hn => hT t hn ht)
    exact List.mem_range.mpr hlt
  · rintro ⟨times, htimes⟩
    let T := times.foldr Nat.max 0 + 1
    refine ⟨T, ?_⟩
    intro t ht hbeep
    have hm := htimes t hbeep
    have hbound : ∀ (xs : List Nat) (x : Nat), x ∈ xs → x ≤ xs.foldr Nat.max 0 := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih =>
        intro x hx
        simp only [List.mem_cons] at hx
        simp only [List.foldr_cons]
        rcases hx with rfl | hx
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)
    have hb := hbound times t hm
    omega

/-- Adding or dropping a finite initial segment does not affect eventual silence. -/
theorem eventuallySilent_iff_shift (k : Nat) :
    M.EventuallySilent ↔ ∃ T, ∀ t, T ≤ t → ¬ M.BeepAt (k + t) := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, fun t ht => hT (k + t) (by omega)⟩
  · rintro ⟨T, hT⟩
    refine ⟨k + T, ?_⟩
    intro t ht
    have heq : k + (t - k) = t := by omega
    rw [← heq]
    exact hT (t - k) (by omega)

end EventSystem
end Shared.Beeping
