import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

/-! The exact public statement. `Nat.nth Nat.Prime 0 = 2`; rank 0 below
therefore denotes the next prime. The tail hypothesis in the composition
lemma is an OPEN INTERNAL OBLIGATION, not an analytic import. -/
namespace Sude

noncomputable section

abbrev Cell (n : ℕ) := Fin n × Fin n

def oddPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i + 1)

def pool (n : ℕ) : Set ℕ := Set.range (fun i : Fin (n * n) => oddPrime i.val)

def entry {n : ℕ} (a : Cell n ≃ Fin (n * n)) (c : Cell n) : ℕ :=
  oddPrime (a c).val

def rowSum {n : ℕ} (a : Cell n ≃ Fin (n * n)) (i : Fin n) : ℕ :=
  ∑ j : Fin n, entry a (i, j)

def columnSum {n : ℕ} (a : Cell n ≃ Fin (n * n)) (j : Fin n) : ℕ :=
  ∑ i : Fin n, entry a (i, j)

def mainSum {n : ℕ} (a : Cell n ≃ Fin (n * n)) : ℕ :=
  ∑ i : Fin n, entry a (i, i)

def antiSum {n : ℕ} (a : Cell n ≃ Fin (n * n)) : ℕ :=
  ∑ i : Fin n, entry a (i, i.rev)

def Valid {n : ℕ} (a : Cell n ≃ Fin (n * n)) : Prop :=
  (∀ i, Nat.Prime (rowSum a i)) ∧
  (∀ j, Nat.Prime (columnSum a j)) ∧
  Nat.Prime (mainSum a) ∧ Nat.Prime (antiSum a)

def HasSquare (n : ℕ) : Prop := ∃ a : Cell n ≃ Fin (n * n), Valid a

def FiniteWitness : Prop := ∀ n, 0 < n → Odd n → n < 2000 → HasSquare n

def TailObligation : Prop := ∀ n, 2001 ≤ n → Odd n → HasSquare n

theorem oddPrime_injective : Function.Injective oddPrime := by
  intro i j h
  have hi : i + 1 = j + 1 := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
  omega

theorem entry_injective {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    Function.Injective (entry a) := by
  intro x y h
  apply a.injective
  apply Fin.ext
  exact oddPrime_injective h

theorem entry_range {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    Set.range (entry a) = pool n := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨a c, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨a.symm i, by simp [entry]⟩

/-- The rank enumeration is a bijection onto the prescribed value pool. -/
def poolEquiv (n : ℕ) : Fin (n * n) ≃ pool n :=
  Equiv.ofInjective (fun i : Fin (n * n) => oddPrime i.val) (by
    intro i j h
    exact Fin.ext (oddPrime_injective h))

@[simp] theorem poolEquiv_val (n : ℕ) (i : Fin (n * n)) :
    ((poolEquiv n) i).val = oddPrime i.val := rfl

@[simp] theorem poolEquiv_symm_val (n : ℕ) (p : pool n) :
    oddPrime ((poolEquiv n).symm p).val = p.val := by
  simpa only [poolEquiv_val] using congrArg Subtype.val ((poolEquiv n).apply_symm_apply p)

/-- Public, value-oriented statement: every labelled cell is sent to one
value of the prescribed pool, bijectively. -/
def ValuesValid {n : ℕ} (b : Cell n ≃ pool n) : Prop :=
  (∀ i : Fin n, Nat.Prime (∑ j : Fin n, (b (i, j)).val)) ∧
  (∀ j : Fin n, Nat.Prime (∑ i : Fin n, (b (i, j)).val)) ∧
  Nat.Prime (∑ i : Fin n, (b (i, i)).val) ∧
  Nat.Prime (∑ i : Fin n, (b (i, i.rev)).val)

theorem hasSquare_iff_values (n : ℕ) :
    HasSquare n ↔ ∃ b : Cell n ≃ pool n, ValuesValid b := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.trans (poolEquiv n), ?_⟩
    simpa [ValuesValid, Valid, rowSum, columnSum, mainSum, antiSum, entry]
      using ha
  · rintro ⟨b, hb⟩
    refine ⟨b.trans (poolEquiv n).symm, ?_⟩
    simpa [ValuesValid, Valid, rowSum, columnSum, mainSum, antiSum, entry] using hb

theorem square_one : HasSquare 1 := by
  let a : Cell 1 ≃ Fin (1 * 1) := {
    toFun := fun _ => 0
    invFun := fun _ => (0, 0)
    left_inv := by
      rintro ⟨i, j⟩
      simp [Fin.eq_zero i, Fin.eq_zero j]
    right_inv := by
      intro i
      exact (Fin.eq_zero i).symm }
  have hentry (c : Cell 1) : entry a c = 3 := by
    have h : a c = 0 := Fin.eq_zero (a c)
    simp [entry, oddPrime, h]
  refine ⟨a, ?_⟩
  simp [Valid, rowSum, columnSum, mainSum, antiSum, hentry,
    Nat.prime_three]

/-- A provisional composition milestone. `tail` is *not* a permitted
external import; proving it from the published imports is the main task. -/
theorem compose_finite_and_open_tail (finite : FiniteWitness) (tail : TailObligation) :
    ∀ n, 0 < n → Odd n → HasSquare n := by
  intro n positive odd
  by_cases h : n < 2000
  · exact finite n positive odd h
  · apply tail n ?_ odd
    obtain ⟨k, hk⟩ := odd
    omega

end

end Sude
