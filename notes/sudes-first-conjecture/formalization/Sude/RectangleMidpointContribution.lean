import Sude.PrefixRectangleInvoice
import Sude.PermutedSeedMidpoints

/-! Retain both endpoint orientations in actual rectangle line contributions. -/
namespace Sude
noncomputable section

/-- The actual contribution of one oriented rectangle pair to a labelled line. -/
noncomputable def rectanglePairContribution {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (p : Fin L × Fin 2)
    (low high : ℝ) : ℝ := by
  classical
  exact (if line (packedRectangleCorner hs choice (p.1, prefixPairCorner p.2 false)) then low else 0) +
    (if line (packedRectangleCorner hs choice (p.1, prefixPairCorner p.2 true)) then high else 0)

/-- The signed high-endpoint incidence minus low-endpoint incidence. -/
noncomputable def rectanglePairOrientation {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (p : Fin L × Fin 2) : ℝ := by
  classical
  exact (if line (packedRectangleCorner hs choice (p.1, prefixPairCorner p.2 true)) then 1 else 0) -
    (if line (packedRectangleCorner hs choice (p.1, prefixPairCorner p.2 false)) then 1 else 0)

/-- Every actual rectangle-pair contribution is its weighted midpoint plus
its signed half-gap, including the reversed orientation of the second pair. -/
theorem rectanglePairContribution_midpoint {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (p : Fin L × Fin 2) (low high : ℝ) :
    rectanglePairContribution hs choice line p low high =
      rectanglePairWeight hs choice line p * ((low + high) / 2) +
        rectanglePairOrientation hs choice line p * ((high - low) / 2) := by
  classical
  unfold rectanglePairContribution rectanglePairWeight rectanglePairOrientation
  split_ifs <;> ring

/-- With an actual placed retained pair, the midpoint term uses the same
stage permutation and the signed gap is the genuine fixed pair difference. -/
theorem placedRectangleContribution_midpoint {n r P Q gap d L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (ω : Fin P → Equiv.Perm (Fin Q)) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (line : Cell n → Prop) (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : Fin (P * (4 * d)) × Fin 4,
      entry a (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixRectangleInput hdiag x)).val)
    (j : Fin P) (rect : Fin (4 * d)) (pair : Fin 2) :
    let p := prefixRectanglePairSlot hrect ((j, rect), pair)
    rectanglePairContribution hs choice line p
      (entry a (packedRectangleCorner hs choice (p.1, prefixPairCorner pair false)))
      (entry a (packedRectangleCorner hs choice (p.1, prefixPairCorner pair true))) =
      rectanglePairWeight hs choice line p *
        retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j
          (ω j (prefixDiagonalPairIndex hdiag (rect, pair))) +
      rectanglePairOrientation hs choice line p * ((gap : ℝ) / 2) := by
  dsimp only
  rw [rectanglePairContribution_midpoint]
  have hm := permutedSeed_placed_rectangle_midpoint candidates hcard kept hsub hkept initial hav ω hdiag a
    (fun x => packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) hplaced j rect pair
  have hg : (entry a (packedRectangleCorner hs choice
        (Fin.castLE hrect (finProdFinEquiv (j, rect)), prefixPairCorner pair true)) : ℝ) -
      entry a (packedRectangleCorner hs choice
        (Fin.castLE hrect (finProdFinEquiv (j, rect)), prefixPairCorner pair false)) = gap := by
    rw [hplaced (finProdFinEquiv (j, rect), prefixPairCorner pair true),
      hplaced (finProdFinEquiv (j, rect), prefixPairCorner pair false),
      prefixRectangleInput_pair, prefixRectangleInput_pair]
    have h := permutedRetainedSeedValues_gap candidates r P Q gap hcard kept hsub hkept initial hav ω
      j (prefixDiagonalPairIndex hdiag (rect, pair))
    have hreal : ((permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        ((j, prefixDiagonalPairIndex hdiag (rect, pair)), true)).val : ℝ) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        ((j, prefixDiagonalPairIndex hdiag (rect, pair)), false)).val + gap := by
      exact_mod_cast h
    linarith
  simpa [prefixRectanglePairSlot] using congrArg₂ (fun x y =>
    rectanglePairWeight hs choice line (prefixRectanglePairSlot hrect ((j, rect), pair)) * x +
    rectanglePairOrientation hs choice line (prefixRectanglePairSlot hrect ((j, rect), pair)) * (y / 2)) hm hg

end
end Sude
