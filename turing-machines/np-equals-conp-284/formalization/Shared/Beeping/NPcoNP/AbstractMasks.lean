import Mathlib.Tactic

/-!
A finite abstract domain for the retained-register invariant in the pinned
284-state producer's independent checker. Categories represent exactly zero,
exactly one, and all naturals at least two. The finite image tables here are
proved sound for *every* natural, including all parities of large values.
They do not yet verify the producer's stored invariant or grammar edges.
-/

namespace Shared.Beeping.NPcoNP.AbstractMasks

inductive Category where
  | zero | one | many
  deriving DecidableEq, Repr

open Category

def category : Nat → Category
  | 0 => zero
  | 1 => one
  | _ + 2 => many

/-- The checker uses a three-bit set of possible categories. Finsets give
the same finite powerset without conflating the empty and zero categories. -/
abbrev Mask := Finset Category

def admits (m : Mask) (n : Nat) : Prop := category n ∈ m

def incImage : Category → Mask
  | zero => {one}
  | one => {many}
  | many => {many}

/-- The Boolean is true for the unsuccessful zero branch. -/
def decImage : Category → Bool → Mask
  | zero, true => {zero}
  | one, false => {zero}
  | many, false => {one, many}
  | _, _ => ∅

/-- The Boolean is true on even inputs, matching the checker's skip arm. -/
def halfImage : Category → Bool → Mask
  | zero, true => {zero}
  | one, false => {zero}
  | many, _ => {one, many}
  | _, _ => ∅

theorem inc_sound (n : Nat) : category (n+1) ∈ incImage (category n) := by
  cases n with
  | zero => simp [category, incImage]
  | succ n => cases n <;> simp [category, incImage]

theorem dec_sound (n : Nat) :
    category (n-1) ∈ decImage (category n) (n == 0) := by
  cases n with
  | zero => simp [category, decImage]
  | succ n =>
    cases n with
    | zero => simp [category, decImage]
    | succ n => cases n <;> simp [category, decImage]

theorem half_sound (n : Nat) :
    category (n/2) ∈ halfImage (category n) (n % 2 == 0) := by
  cases n with
  | zero => simp [category, halfImage]
  | succ n =>
    cases n with
    | zero => simp [category, halfImage]
    | succ n =>
      simp only [category, halfImage, Finset.mem_insert, Finset.mem_singleton]
      have h : 0 < (n+2)/2 := by omega
      cases hq : (n+2)/2 with
      | zero => omega
      | succ k => cases k <;> simp [category]

def lift (image : Category → Mask) (m : Mask) : Mask := m.biUnion image

theorem inc_mask_sound (m : Mask) (n : Nat) (h : admits m n) :
    admits (lift incImage m) (n+1) := by
  exact Finset.mem_biUnion.mpr ⟨category n, h, inc_sound n⟩

theorem dec_mask_sound (m : Mask) (n : Nat) (h : admits m n) :
    admits (lift (fun k => decImage k (n == 0)) m) (n-1) := by
  exact Finset.mem_biUnion.mpr ⟨category n, h, dec_sound n⟩

theorem half_mask_sound (m : Mask) (n : Nat) (h : admits m n) :
    admits (lift (fun k => halfImage k (n % 2 == 0)) m) (n/2) := by
  exact Finset.mem_biUnion.mpr ⟨category n, h, half_sound n⟩

theorem only_zero {n : Nat} (h : admits {zero} n) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> simp [admits, category] at h

/-- The local outside-entry fact: a HALF on a distinct coordinate preserves
an already established zero work coordinate. Establishing the premise from
the actual reachable graph and binding its indices are separate obligations. -/
theorem half_preserves_zero_work {ι : Type} [DecidableEq ι]
    (s : ι → Nat) (operand work : ι) (hne : work ≠ operand)
    (hz : admits {zero} (s work)) :
    (Function.update s operand (s operand / 2)) work = 0 := by
  rw [Function.update_of_ne hne]
  exact only_zero hz

end Shared.Beeping.NPcoNP.AbstractMasks
