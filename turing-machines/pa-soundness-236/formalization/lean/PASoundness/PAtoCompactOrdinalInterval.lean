import PASoundness.HFCoding
import Mathlib.Order.Interval.Finset.Nat

/-! A standard-HF ordinal interval for a proposed addition relation.

This is semantic calibration only. It does not construct a K suffix filter,
an isomorphism graph, quotient congruence, or object-level PA arithmetic.
In particular, compact code 1 is literally `member 0 0`, so the ordinary
complement used here has not been justified as negation in arbitrary K models. -/
namespace PASoundness.PAtoCompactOrdinalInterval
open PASoundness.HFCoding

/-- The HF object whose members are exactly the ordinals indexed in `[l,k)`. -/
def ordinalInterval (l k : Nat) : Object :=
  assemble ((Finset.Ico l k).image ordinal)

/-- Explicit membership, valid even when the interval is empty. -/
theorem mem_interval (x : Object) (l k : Nat) :
    x ∈ ordinalInterval l k ↔ ∃ n, l ≤ n ∧ n < k ∧ x = ordinal n := by
  simp only [ordinalInterval, mem_assemble, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨n,⟨hl,hk⟩,hn⟩
    exact ⟨n,hl,hk,hn.symm⟩
  · rintro ⟨n,hl,hk,rfl⟩
    exact ⟨n,⟨hl,hk⟩,rfl⟩

/-- In standard HF this interval is the ordinal difference `k \ l`. -/
theorem mem_interval_iff_difference (x : Object) (l k : Nat) :
    x ∈ ordinalInterval l k ↔ x ∈ ordinal k ∧ x ∉ ordinal l := by
  constructor
  · intro h
    obtain ⟨n,hl,hk,rfl⟩ := (mem_interval x l k).mp h
    exact ⟨ordinal_member hk, by simpa using (show ¬ n < l by omega)⟩
  · rintro ⟨hk,hl⟩
    obtain ⟨n,hn,rfl⟩ := (mem_ordinal x k).mp hk
    have hnl : l ≤ n := by
      have hnot : ¬ n < l := by simpa using hl
      omega
    exact (mem_interval _ _ _).mpr ⟨n,hnl,hn,rfl⟩

/-- The interval has exactly `k-l` members; this is a finite-set calculation,
not a derivation in the compact calculus. -/
theorem interval_card (l k : Nat) : (elements (ordinalInterval l k)).card = k - l := by
  rw [ordinalInterval, elements_assemble, Finset.card_image_iff.mpr]
  · simp
  · exact ordinal_injective.injOn

/-- Its induced membership order agrees with the usual order on the indices. -/
theorem interval_order (m n l k : Nat) (hm : l ≤ m ∧ m < k)
    (hn : l ≤ n ∧ n < k) :
    ordinal m ∈ ordinalInterval l k ∧ ordinal n ∈ ordinalInterval l k ∧
      (ordinal m ∈ ordinal n ↔ m < n) := by
  exact ⟨(mem_interval _ _ _).mpr ⟨m,hm.1,hm.2,rfl⟩,
    (mem_interval _ _ _).mpr ⟨n,hn.1,hn.2,rfl⟩, ordinal_mem_ordinal m n⟩

/-- The shift `r ↦ ordinal(l+r)` explicitly enumerates the interval in
membership order. This is an external standard-HF relation, not a
represented graph or an object-level K isomorphism. -/
theorem interval_shift_order (l k : Nat) :
    (∀ r, r < k-l → ordinal (l+r) ∈ ordinalInterval l k) ∧
    (∀ x, x ∈ ordinalInterval l k → ∃ r, r < k-l ∧ x = ordinal (l+r)) ∧
    (∀ r s, ordinal (l+r) ∈ ordinal (l+s) ↔ r < s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact (mem_interval _ _ _).mpr ⟨l+r, by omega, by omega, rfl⟩
  · intro x hx
    obtain ⟨n,hl,hk,he⟩ := (mem_interval x l k).mp hx
    refine ⟨n-l, by omega, ?_⟩
    simpa [Nat.add_sub_of_le hl] using he
  · intro r s
    simp

end PASoundness.PAtoCompactOrdinalInterval

#print axioms PASoundness.PAtoCompactOrdinalInterval.mem_interval_iff_difference
#print axioms PASoundness.PAtoCompactOrdinalInterval.interval_card
#print axioms PASoundness.PAtoCompactOrdinalInterval.interval_order
#print axioms PASoundness.PAtoCompactOrdinalInterval.interval_shift_order
