import Shared.Beeping.NPcoNP.Source284Parser

/-! The finite-search part of the 284 source's oversized reference witness
enumeration. The comparison below is valid for every Boolean predicate that
is invariant under truncating its input to the low `C` bits. Establishing
that premise for the source's concrete relative-direction simulator is a
separate obligation. -/
namespace Shared.Beeping.NPcoNP.Source284Parser

/-- Enlarging a finite witness range beyond `2^C` does not change an
existential search if all witnesses have the same truth value as their
low-`C`-bit truncation. -/
theorem range_any_oversupply (C B : Nat) (P : Nat → Bool)
    (hB : 2 ^ C ≤ B) (htruncate : ∀ b, P b = P (b % 2 ^ C)) :
    (List.range B).any P = (List.range (2 ^ C)).any P := by
  have hpositive : 0 < 2 ^ C := by positivity
  have hiff : ((List.range B).any P = true) ↔
      ((List.range (2 ^ C)).any P = true) := by
    simp only [List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨b, _, hb⟩
      refine ⟨b % 2 ^ C, Nat.mod_lt _ hpositive, ?_⟩
      rw [← htruncate b]
      exact hb
    · rintro ⟨b, hb, hp⟩
      exact ⟨b, Nat.lt_of_lt_of_le hb hB, hp⟩
  cases hleft : (List.range B).any P <;>
    cases hright : (List.range (2 ^ C)).any P <;> simp_all

/-- The pinned source uses `D(i)` attempts with clock `N(i)`. Its sentinel
bound meets the generic oversupply premise, including `N(i) = 0`. -/
theorem reference_range_oversupply (i : Nat) (P : Nat → Bool)
    (htruncate : ∀ b, P b = P (b % 2 ^ length i)) :
    (List.range (description i)).any P = (List.range (2 ^ length i)).any P :=
  range_any_oversupply (length i) (description i) P (sentinel_bounds i).1 htruncate

end Shared.Beeping.NPcoNP.Source284Parser
