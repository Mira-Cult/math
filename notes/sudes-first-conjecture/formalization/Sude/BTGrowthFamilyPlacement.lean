import Sude.BTGrowingPermutedPlacement
import Sude.BTGrowthSelectedLabelIndices
import Sude.DisjointFamilyPermutation

/-! Allocate supplied disjoint stage-label families to supplied physical pair
slot families on one existing growth-trace square. -/
namespace Sude
noncomputable section

/-- Given stagewise disjoint label families and equally sized disjoint slot
families, realize a single stage-preserving permutation on the supplied
square. The same trace endpoints move as whole pairs, and every cell outside
the growth role is fixed. This does not choose the families or establish any
geometric interpretation or line bound for the supplied slots. -/
theorem bt_growth_family_placement
    {g Q n P d r L : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (offset : ℕ) (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P * r) (hc : cols.length = P * r)
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : PrefixPhysicalInputs P d r n,
      entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Fin P → ι → Finset (Fin Q)) (T : Fin P → ι → Finset ℕ)
    (hsub : ∀ j t, T j t ⊆ (BTStageTrace.stageAt stages hlen j).lows)
    (hS : ∀ j t u, t ≠ u → Disjoint (S j t) (S j u))
    (hT : ∀ j t u, t ≠ u → Disjoint (T j t) (T j u))
    (hcard : ∀ j t, (S j t).card = (T j t).card) :
    let cells := btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc
    ∃ (ω : Fin P → Equiv.Perm (Fin Q)) (a' : Cell n ≃ Fin (n*n)),
      (∀ j t, (S j t).image (fun i => trace.lowAt hlen j (ω j i)) = T j t) ∧
      (∀ x, entry a' (cells x) = (trace.poolValues hlen hpool (stagePairPermutation ω x)).val) ∧
      (∀ x : PrefixPhysicalInputs P d r n,
        entry a' (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
          (trace.poolValues hlen hpool (stagePairPermutation ω (prefixPhysicalInput hfit hdiag x))).val) ∧
      (∀ c, c ∉ Set.range cells → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : Fin Q × Bool => entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin Q × Bool => entry a (cells ((j,x.1),x.2)))) ∧
      (∀ j i, entry a' (cells ((j,i),true)) =
        entry a' (cells ((j,i),false)) + (BTStageTrace.stageAt stages hlen j).gap) := by
  classical
  dsimp only
  obtain ⟨I, himage, hicard, hidis⟩ := bt_growth_selected_label_indices trace hlen T hsub
  have hex : ∀ j, ∃ σ : Equiv.Perm (Fin Q), ∀ t, (S j t).image σ = I j t := by
    intro j
    obtain ⟨σ, hσ, _⟩ := disjoint_family_permutation (S j) (I j) (hS j)
      (fun t u hne => hidis j t u (hT j t u hne))
      (fun t => (hcard j t).trans (hicard j t).symm)
    exact ⟨σ, hσ⟩
  choose ω hω using hex
  obtain ⟨a', hperm, hphys, hfix, hstage, hgap⟩ := bt_growing_permuted_placement
    trace hlen hpool hfit hdiag hexact offset hoff hs choice rows cols hr hc a hplaced ω
  refine ⟨ω, a', ?_, hperm, hphys, hfix, hstage, hgap⟩
  intro j t
  calc
    (S j t).image (fun i => trace.lowAt hlen j (ω j i)) =
        ((S j t).image (ω j)).image (trace.lowAt hlen j) := by rw [Finset.image_image]; rfl
    _ = T j t := by rw [hω j t, himage j t]

end
end Sude
