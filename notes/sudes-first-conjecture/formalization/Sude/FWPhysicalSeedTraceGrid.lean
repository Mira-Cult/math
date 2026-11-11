import Sude.FWSeedTraceGridExact
import Sude.FWBridgeSeedFullPlacement

namespace Sude
noncomputable section
local instance fwPhysicalSeedTraceStageDecidable : DecidableEq BTSelectedStage := Classical.decEq _

/-- One actual diagonal pair slot for each retained seed stage. -/
def fwPhysicalSeedCell {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (i : Fin 16) (side : Bool) : Cell n :=
  packedRectangleCorner hs choice
    (fwSeedRectangle hseed (finProdFinEquiv (i, (0 : Fin (4 * 6)))),
      prefixPairCorner (0 : Fin 2) side)

/-- The lower and upper entry values at that physical pair slot. -/
def fwPhysicalSeedLabel {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (i : Fin 16) : ℕ × ℕ :=
  (entry a (fwPhysicalSeedCell hseed hs choice i false),
    entry a (fwPhysicalSeedCell hseed hs choice i true))

/-- Gap measured from the actual ordered entry values. -/
def fwPhysicalSeedLabelGap (label : ℕ × ℕ) : ℕ := label.2 - label.1

/-- Distinct retained stages have distinct value-pair labels. -/
theorem fwPhysicalSeedLabel_injective {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) :
    Function.Injective (fwPhysicalSeedLabel hseed hs choice a) := by
  intro i j hij
  have hv := congrArg Prod.fst hij
  have hc : fwPhysicalSeedCell hseed hs choice i false =
      fwPhysicalSeedCell hseed hs choice j false := (entry_injective a) hv
  have hc' := packedRectangleCorner_injective hs choice hc
  have hr := fwSeedRectangle_injective hseed (congrArg Prod.fst hc')
  exact congrArg Prod.fst (finProdFinEquiv.injective hr)

/-- Sixteen actual gap-two entry pairs supply the initial even grid. -/
theorem fw_physical_sixteen_seed_even_grid {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n))
    (hgap : ∀ i : Fin 16, entry a (fwPhysicalSeedCell hseed hs choice i true) =
      entry a (fwPhysicalSeedCell hseed hs choice i false) + 2) :
    CompleteEvenGrid (Finset.univ.image (fwPhysicalSeedLabel hseed hs choice a))
      fwPhysicalSeedLabelGap 32 := by
  apply fw_sixteen_supplied_seed_even_grid _ _ (fwPhysicalSeedLabel_injective hseed hs choice a)
  intro i
  dsimp [fwPhysicalSeedLabelGap, fwPhysicalSeedLabel]
  rw [hgap i]
  omega

/-- The gap-two equation exposed by joint FW placement, specialized to one
physical diagonal pair in each retained seed stage. -/
theorem fwPhysicalSeedLabel_gap {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ (j : Fin 16) (u : Fin (4 * 6)) (pair : Fin 2),
      entry a (packedRectangleCorner hs choice
        (fwSeedRectangle hseed (finProdFinEquiv (j, u)), prefixPairCorner pair true)) =
      entry a (packedRectangleCorner hs choice
        (fwSeedRectangle hseed (finProdFinEquiv (j, u)), prefixPairCorner pair false)) + 2) :
    ∀ i, fwPhysicalSeedLabelGap (fwPhysicalSeedLabel hseed hs choice a i) = 2 := by
  intro i
  have hgap : entry a (fwPhysicalSeedCell hseed hs choice i true) =
      entry a (fwPhysicalSeedCell hseed hs choice i false) + 2 := hplaced i 0 0
  dsimp [fwPhysicalSeedLabelGap, fwPhysicalSeedLabel]
  rw [hgap]
  omega

/-- An actual joint-placement seed family and any supplied growth trace from
radius 32 yield a tagged complete even grid to the actual final radius. The
seed labels are physical entry pairs; trace labels are tagged separately.
The trace is supplied independently; this does not prove its disjointness
from seed entries or install growth stages in physical cells. -/
theorem fw_physical_seed_trace_even_grid {n L Q : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ (j : Fin 16) (u : Fin (4 * 6)) (pair : Fin 2),
      entry a (packedRectangleCorner hs choice
        (fwSeedRectangle hseed (finProdFinEquiv (j, u)), prefixPairCorner pair true)) =
      entry a (packedRectangleCorner hs choice
        (fwSeedRectangle hseed (finProdFinEquiv (j, u)), prefixPairCorner pair false)) + 2)
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (hQ : 0 < Q) (trace : BTGrowingTrace 2 Q initial 32 final last stages) :
    let gap : Sum (ℕ × ℕ) BTSelectedStage → ℕ := Sum.elim fwPhysicalSeedLabelGap BTSelectedStage.gap
    let base := Finset.univ.image (fun i => Sum.inl (fwPhysicalSeedLabel hseed hs choice a i) :
      Fin 16 → Sum (ℕ × ℕ) BTSelectedStage)
    let labels : List (Sum (ℕ × ℕ) BTSelectedStage) := stages.map Sum.inr
    CompleteEvenGrid (base ∪ labels.toFinset) gap last ∧ 2 ∣ last := by
  exact fw_supplied_seed_trace_even_grid (fwPhysicalSeedLabel hseed hs choice a)
    fwPhysicalSeedLabelGap (fwPhysicalSeedLabel_injective hseed hs choice a)
    (fwPhysicalSeedLabel_gap hseed hs choice a hplaced) hQ trace


end
end Sude
