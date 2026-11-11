import Sude.FWCanonicalSeedGrowthLabels

/-! Disjointness of the canonical physical labels of the actual families.
No gap, grid, radius, CY or primality claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- A canonical seed or growth label never equals a bridge label. -/
theorem fw_canonical_seed_growth_ne_bridge {n : ℕ}
    {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (x : {x // x ∈ fwSeedTraceLabels f.stages}) (j : Fin 5) :
    fwCanonicalSeedGrowthLabel f side x ≠
      bridgeDiagonalRectangle f.hrect (finProdFinEquiv (j, fwCanonicalChoiceRectangle side)) := by
  classical
  rcases x with ⟨x,hx⟩
  cases x with
  | inl s =>
    exact (fw_bridge_seed_rectangle_ne f.hrect f.hseedrect _ _).symm
  | inr s =>
    intro h
    dsimp only [fwCanonicalSeedGrowthLabel] at h
    have hv := congrArg Fin.val h
    have hb := (finProdFinEquiv (j, fwCanonicalChoiceRectangle side) : Fin (5*(4*6))).isLt
    simp only [bridgeDiagonalRectangle, Fin.val_castLE, btGrowingOffsetRectangle] at hv
    omega

/-- A canonical seed or growth label never equals a wide label. -/
theorem fw_canonical_seed_growth_ne_wide {n : ℕ}
    {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (x : {x // x ∈ fwSeedTraceLabels f.stages}) (j : Fin (3*(n/450))) :
    fwCanonicalSeedGrowthLabel f side x ≠
      fwWideRectangle f.hwide (finProdFinEquiv (j, fwCanonicalChoiceRectangle side)) := by
  classical
  rcases x with ⟨x,hx⟩
  cases x with
  | inl s =>
    exact fw_seed_wide_rectangle_ne f.hseedrect f.hwide _ _
  | inr s =>
    intro h
    dsimp only [fwCanonicalSeedGrowthLabel] at h
    have hv := congrArg Fin.val h
    have hw := (finProdFinEquiv (j, fwCanonicalChoiceRectangle side) : Fin ((3*(n/450))*(4*6))).isLt
    simp only [fwWideRectangle, btGrowingOffsetRectangle] at hv
    omega

/-- Canonical bridge and wide labels are in disjoint intervals. -/
theorem fw_canonical_bridge_ne_wide {n : ℕ}
    {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (j : Fin 5) (k : Fin (3*(n/450))) :
    bridgeDiagonalRectangle f.hrect (finProdFinEquiv (j, fwCanonicalChoiceRectangle side)) ≠
      fwWideRectangle f.hwide (finProdFinEquiv (k, fwCanonicalChoiceRectangle side)) :=
  fw_bridge_wide_rectangle_ne f.hrect f.hwide _ _

end
end Sude
