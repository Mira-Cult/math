import Sude.PrefixPopulationCoverage

/-! Restrict a certified full FPF profile to the exact order-dependent prefix. -/
namespace Sude
noncomputable section

/-- The source profile keeps the first `6 * (n + 8)` pairs at every stage. -/
def prefixTruncationIndex {P Q q : ℕ} (h : q ≤ Q) :
    (Fin P × Fin q) × Bool → (Fin P × Fin Q) × Bool :=
  fun x => ((x.1.1, Fin.castLE h x.1.2), x.2)

theorem prefixTruncationIndex_injective {P Q q : ℕ} (h : q ≤ Q) :
    Function.Injective (prefixTruncationIndex (P := P) h) := by
  intro x y heq
  rcases x with ⟨⟨j, i⟩, s⟩
  rcases y with ⟨⟨j', i'⟩, s'⟩
  have hj : j = j' := congrArg (fun z => z.1.1) heq
  have hi : i = i' := Fin.castLE_injective h (congrArg (fun z => z.1.2) heq)
  have hs : s = s' := congrArg Prod.snd heq
  cases hj
  cases hi
  cases hs
  rfl

/-- Restricting a full certified profile preserves global endpoint injectivity. -/
def truncatePrefixValues {P Q q n : ℕ} (h : q ≤ Q)
    (values : (Fin P × Fin Q) × Bool → pool n) :
    (Fin P × Fin q) × Bool → pool n := values ∘ prefixTruncationIndex h

theorem truncatePrefixValues_injective {P Q q n : ℕ} (h : q ≤ Q)
    (values : (Fin P × Fin Q) × Bool → pool n) (hinj : Function.Injective values) :
    Function.Injective (truncatePrefixValues h values) :=
  hinj.comp (prefixTruncationIndex_injective h)

theorem truncatePrefixValues_gap {P Q q n : ℕ} (h : q ≤ Q)
    (values : (Fin P × Fin Q) × Bool → pool n)
    (hgap : ∀ j i, (values ((j, i), true)).val =
      (values ((j, i), false)).val + 2 ^ (j.val + 1)) :
    ∀ j i, (truncatePrefixValues h values ((j, i), true)).val =
      (truncatePrefixValues h values ((j, i), false)).val + 2 ^ (j.val + 1) := by
  intro j i
  exact hgap j (Fin.castLE h i)

/-- Every retained endpoint is one of the full profile's endpoints. -/
theorem truncatePrefixValues_mem_full {P Q q n : ℕ} (h : q ≤ Q)
    (values : (Fin P × Fin Q) × Bool → pool n) (x : (Fin P × Fin q) × Bool) :
    (truncatePrefixValues h values x).val ∈
      (Finset.univ : Finset ((Fin P × Fin Q) × Bool)).image (fun y => (values y).val) := by
  exact Finset.mem_image.mpr ⟨prefixTruncationIndex h x, Finset.mem_univ _, rfl⟩

/-- An endpoint in the unused suffix is not reserved by the truncation.
This uses injectivity of the entire supplied profile. -/
theorem truncatePrefixValues_suffix_free {P Q q n : ℕ} (h : q ≤ Q)
    (values : (Fin P × Fin Q) × Bool → pool n) (hinj : Function.Injective values)
    (j : Fin P) (i : Fin Q) (side : Bool) (hi : q ≤ i.val) :
    (values ((j, i), side)).val ∉
      (Finset.univ : Finset ((Fin P × Fin q) × Bool)).image
        (fun x => (truncatePrefixValues h values x).val) := by
  intro hmem
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
  have heq : prefixTruncationIndex h x = ((j, i), side) := by
    apply hinj
    apply Subtype.ext
    exact hx
  have hv := congrArg (fun z => z.1.2.val) heq
  have hxlt := x.1.2.isLt
  simp only [prefixTruncationIndex, Fin.val_castLE] at hv
  omega

/-- Exact source truncation for every order in a profile's order band. -/
theorem finitePrefix_order_size {n nmax : ℕ} (hn : n ≤ nmax) :
    6 * (n + 8) ≤ 6 * (nmax + 8) := by omega

/-- The deletion budget counts exactly the retained endpoints, not the unused
profile suffix. -/
theorem truncatePrefixValues_card {P Q q n : ℕ} (h : q ≤ Q)
    (values : (Fin P × Fin Q) × Bool → pool n) (hinj : Function.Injective values) :
    ((Finset.univ : Finset ((Fin P × Fin q) × Bool)).image
      (fun x => (truncatePrefixValues h values x).val)).card = 2 * q * P :=
  prefixPopulation_card (truncatePrefixValues h values) (truncatePrefixValues_injective h values hinj)

end
end Sude
