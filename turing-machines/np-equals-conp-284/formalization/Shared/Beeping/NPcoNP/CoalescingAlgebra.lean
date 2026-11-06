import Shared.Beeping.RegisterMachine
import Mathlib.Tactic

/-! Generic register-coalescence algebra. A physical carrier holds the sum of
its logical aliases. Access is valid only when every other alias in the same
fiber is zero. No ownership invariant, producer map, or machine simulation is
asserted here. -/

namespace Shared.Beeping.NPcoNP.CoalescingAlgebra
open PASoundness.RegisterMachine

def pack {n m : Nat} (f : Fin n → Fin m) (b : Bank n) : Bank m :=
  fun j => ∑ i : Fin n, if f i = j then b i else 0

def Exclusive {n m : Nat} (f : Fin n → Fin m) (b : Bank n) (r : Fin n) : Prop :=
  ∀ i, f i = f r → i ≠ r → b i = 0

theorem read_of_exclusive {n m : Nat} (f : Fin n → Fin m) (b : Bank n)
    (r : Fin n) (h : Exclusive f b r) : pack f b (f r) = b r := by
  unfold pack
  rw [Finset.sum_eq_single r]
  · simp
  · intro i hi hir
    by_cases hfi : f i = f r
    · simp [hfi, h i hfi hir]
    · simp [hfi]
  · intro hr
    exact False.elim (hr (Finset.mem_univ r))

theorem pack_write_other {n m : Nat} (f : Fin n → Fin m) (b : Bank n)
    (r : Fin n) (v : Nat) (j : Fin m) (h : j ≠ f r) :
    pack f (write b r v) j = pack f b j := by
  unfold pack
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hir : i = r
  · subst i
    simp [Ne.symm h]
  · simp [write, hir]

theorem exclusive_write {n m : Nat} (f : Fin n → Fin m) (b : Bank n)
    (r : Fin n) (v : Nat) (h : Exclusive f b r) :
    Exclusive f (write b r v) r := by
  intro i hfi hir
  simpa [write, hir] using h i hfi hir

theorem pack_write_of_exclusive {n m : Nat} (f : Fin n → Fin m) (b : Bank n)
    (r : Fin n) (v : Nat) (h : Exclusive f b r) :
    pack f (write b r v) = write (pack f b) (f r) v := by
  funext j
  by_cases hj : j = f r
  · subst j
    rw [read_of_exclusive f (write b r v) r (exclusive_write f b r v h)]
    simp [write]
  · rw [pack_write_other f b r v j hj]
    simp [write, hj]

end Shared.Beeping.NPcoNP.CoalescingAlgebra
