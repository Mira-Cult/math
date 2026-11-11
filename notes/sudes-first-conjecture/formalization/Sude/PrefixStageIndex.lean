import Sude.PrefixStageCertificate

/-! Indexed versions of a certified fixed-gap stage. -/
namespace Sude
noncomputable section

/-- Keep the source list order while giving each pair a finite label. -/
def stagePairLabel (xs : List ℕ) (x : Fin xs.length × Bool) :
    {p // p ∈ xs.toFinset} × Bool :=
  (⟨xs.get x.1, List.mem_toFinset.mpr (List.get_mem xs x.1)⟩, x.2)

theorem stagePairLabel_injective (xs : List ℕ) (hnodup : xs.Nodup) :
    Function.Injective (stagePairLabel xs) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  have hget : xs.get i = xs.get j := congrArg (fun z => z.1.val) h
  have hi : i = j := hnodup.injective_get hget
  have hs : s = t := congrArg Prod.snd h
  exact Prod.ext hi hs

/-- The low or high endpoint at a source-list index. -/
def stagePairEndpoint (xs : List ℕ) (gap : ℕ) (x : Fin xs.length × Bool) : ℕ :=
  pairEndpoint xs.toFinset gap (stagePairLabel xs x)

theorem stagePairEndpoint_injective (xs : List ℕ) (gap : ℕ)
    (hnodup : xs.Nodup) (hpos : 0 < gap)
    (hmatch : PairwiseDisjointPairs xs.toFinset gap) :
    Function.Injective (stagePairEndpoint xs gap) :=
  (pairEndpoint_injective xs.toFinset gap hpos hmatch).comp
    (stagePairLabel_injective xs hnodup)

theorem stagePairEndpoint_formula (xs : List ℕ) (gap : ℕ) (i : Fin xs.length) (side : Bool) :
    stagePairEndpoint xs gap (i, side) = xs.get i + if side then gap else 0 := by
  cases side <;> simp [stagePairEndpoint, stagePairLabel, pairEndpoint]

theorem stagePairEndpoint_mem_footprint (xs : List ℕ) (gap : ℕ)
    (x : Fin xs.length × Bool) : stagePairEndpoint xs gap x ∈ pairFootprint xs.toFinset gap := by
  rcases x with ⟨i, side⟩
  have hm : xs.get i ∈ xs.toFinset := List.mem_toFinset.mpr (List.get_mem xs i)
  cases side
  · simp only [stagePairEndpoint_formula, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact Finset.mem_union_left _ hm
  · rw [stagePairEndpoint_formula]
    simp only [↓reduceIte]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨xs.get i, hm, rfl⟩

theorem stagePairEndpoint_mem_pool {n : ℕ} (xs : List ℕ) (gap : ℕ)
    (hpool : ∀ p ∈ xs.toFinset, p ∈ pool n ∧ p + gap ∈ pool n)
    (x : Fin xs.length × Bool) : stagePairEndpoint xs gap x ∈ pool n := by
  rcases x with ⟨i, side⟩
  have h := hpool (xs.get i) (List.mem_toFinset.mpr (List.get_mem xs i))
  cases side
  · simpa [stagePairEndpoint_formula] using h.1
  · simpa [stagePairEndpoint_formula] using h.2

/-- Pool-valued endpoints, preserving the source list's index and side. -/
def stagePairPoolValues {n : ℕ} (xs : List ℕ) (gap : ℕ)
    (hpool : ∀ p ∈ xs.toFinset, p ∈ pool n ∧ p + gap ∈ pool n) :
    Fin xs.length × Bool → pool n := fun x =>
  ⟨stagePairEndpoint xs gap x, stagePairEndpoint_mem_pool xs gap hpool x⟩

theorem stagePairPoolValues_injective {n : ℕ} (xs : List ℕ) (gap : ℕ)
    (hpool : ∀ p ∈ xs.toFinset, p ∈ pool n ∧ p + gap ∈ pool n)
    (hnodup : xs.Nodup) (hpos : 0 < gap)
    (hmatch : PairwiseDisjointPairs xs.toFinset gap) :
    Function.Injective (stagePairPoolValues xs gap hpool) := by
  intro x y h
  exact stagePairEndpoint_injective xs gap hnodup hpos hmatch (congrArg Subtype.val h)

theorem stagePairPoolValues_gap {n : ℕ} (xs : List ℕ) (gap : ℕ)
    (hpool : ∀ p ∈ xs.toFinset, p ∈ pool n ∧ p + gap ∈ pool n)
    (i : Fin xs.length) :
    (stagePairPoolValues xs gap hpool (i, true)).val =
      (stagePairPoolValues xs gap hpool (i, false)).val + gap := by
  simp [stagePairPoolValues, stagePairEndpoint_formula]

end
end Sude
