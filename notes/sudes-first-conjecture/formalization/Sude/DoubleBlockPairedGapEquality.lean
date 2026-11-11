import Sude.FWBridgeWideUnmatchedColumnOrientation

/-! An endpoint equation with one gap per block gives equal real gap
weights for its two labelled physical pairs. No allocation is constructed. -/
namespace Sude
noncomputable section

/-- The two actual pairs in every block have the same real high-minus-low
gap when the same natural-number gap is supplied for both endpoint equations. -/
theorem double_block_paired_gap_equality {n : ℕ} {J B : Type*}
    (cells : (J × B × Fin 2) × Bool → Cell n)
    (a : Cell n ≃ Fin (n * n)) (gap : J → B → ℕ)
    (hgap : ∀ j b p, entry a (cells ((j,b,p),true)) =
      entry a (cells ((j,b,p),false)) + gap j b) :
    ∀ j b,
      (entry a (cells ((j,b,0),true)) : ℝ) - entry a (cells ((j,b,0),false)) =
      (entry a (cells ((j,b,1),true)) : ℝ) - entry a (cells ((j,b,1),false)) := by
  intro j b
  have h0 : (entry a (cells ((j,b,0),true)) : ℝ) =
      (entry a (cells ((j,b,0),false)) : ℝ) + gap j b := by
    exact_mod_cast hgap j b 0
  have h1 : (entry a (cells ((j,b,1),true)) : ℝ) =
      (entry a (cells ((j,b,1),false)) : ℝ) + gap j b := by
    exact_mod_cast hgap j b 1
  linarith

end
end Sude
