import Sude.FWProjectedCYPrimeGrowthDiagonals
import Sude.FWFreshT75ReferenceGains
import Sude.PackedLabelRectangleSupport

/-! Conditional physical diagonal repair on the exact CY and routed output
chosen by one projected witness. Rectangle grids, paired physical gaps and
bounds for the controller-selected reference are still explicit hypotheses;
no target existence or unconditional diagonal primality is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Preserve the original prime-row/column and growth conclusions on one
routed square, then expose a diagonal-repair continuation using its exact CY
square. The final rectangle-trade result is not asserted to retain the
intermediate active-image invariant. -/
theorem fw_projected_cy_prime_growth_diagonal_repair
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (g : FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice f)
    (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (target : Fin n → ℕ) (D : ℝ)
    (hprime : ∀ i, Nat.Prime (target i)) (htargetOdd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ D)
    (hbudget : fwFrozenCYLineRadius n + D ≤
      (518481/500000 : ℝ) * (((n/450)*poolMaximum n : ℕ) : ℝ)) :
    let full := fwThetaFamilyFull f
    let final := full ∪ unreservedDiagonalCells full
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    let μ := fun j => (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6 * (n + 8) : ℕ)
    ∃ diag cy out : Cell n ≃ Fin (n*n),
    (
      (∀ z ∈ full, entry diag z = entry oldReference z) ∧
      (∀ z ∈ final, entry cy z = entry diag z) ∧
      (∀ z ∈ full, entry cy z = entry oldReference z) ∧
      |(mainSum cy : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry oldReference z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum cy : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry oldReference z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      mainSum cy = mainSum diag ∧ antiSum cy = antiSum diag ∧
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum cy ∧ antiSum out = antiSum cy ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ roles, entry out z = entry cy z) ∧
      roles.image (entry out) = roles.image (entry cy) ∧
      (∀ z ∈ unreservedDiagonalCells full, entry out z = entry cy z) ∧
      full.image (entry out) = full.image (entry cy) ∧
      actualUnusedPool out full = actualUnusedPool cy full ∧
    (∀ z ∈ fwThetaFamilyFull f, z ∈ mainCells n ∨ z ∈ antiCells n → entry out z = entry f.ordered z) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) =
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) =
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) =
      (∑ j, ∑ q ∈ g.T j, growthStageMidpoint (f.stages.get j) q) - 6 * ∑ j, ((f.stages.get j).gap : ℝ) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) =
      (∑ j, ∑ q ∈ g.U j, growthStageMidpoint (f.stages.get j) q) - 6 * ∑ j, ((f.stages.get j).gap : ℝ) ∧
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤ ((poolMaximum n : ℝ) / 6) / 2 ∧
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤
        ((n + 8 : ℝ) / (2 * (n + 6))) * ((poolMaximum n : ℝ) / 6)
    ) ∧
    (∀ (gap : Fin (fwJointRectangleCount n 254) → ℕ)
      (labels : Finset (Fin (fwJointRectangleCount n 254))) (Rm Ra : ℕ)
      (keep : Finset (Cell n)) (Udiag : ℝ),
      CompleteEvenGrid (labels.filter fun i => choice i = true) gap Rm →
      CompleteEvenGrid (labels.filter fun i => choice i = false) gap Ra →
      (∀ i ∈ labels,
        entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
          entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) + gap i ∧
        entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
          entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) + gap i) →
      (∀ z ∈ keep, ∀ i ∈ labels,
        z ∉ rectangleCells (RectanglePacking.firstRow f.hs i) (RectanglePacking.secondRow f.hs i)
          (RectanglePacking.firstColumn f.hs choice i) (RectanglePacking.secondColumn f.hs choice i)) →
      ∃ before : Finset (Fin (fwJointRectangleCount n 254)), before ⊆ labels ∧
        let reference := packedTradeSequence f.hs choice cy before.toList
        (mainSum reference : ℤ) - (mainSum cy : ℤ) = evenGridCenter Rm ∧
        (antiSum reference : ℤ) - (antiSum cy : ℤ) = evenGridCenter Ra ∧
        (|(mainSum reference : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ Udiag →
         |(antiSum reference : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ Udiag →
         Udiag + D ≤ (evenGridCenter Rm : ℝ) →
         Udiag + D ≤ (evenGridCenter Ra : ℝ) →
         ∃ (q : ℕ) (result : Cell n ≃ Fin (n*n)),
           Nat.Prime q ∧ (∃ i, q = target i) ∧
           (∀ r, rowSum result r = rowSum out r) ∧
           (∀ c, columnSum result c = columnSum out c) ∧
           mainSum result = q ∧ antiSum result = q ∧ Valid result ∧
           Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
           (∀ z ∈ keep, entry result z = entry out z))) := by
  classical
  obtain ⟨diag, cy, out, hfacts⟩ :=
    fw_projected_cy_prime_targets_growth_diagonals bmor lower upper hnlo hnhi hodd choice
      f p oldReference roles net g hexp target D hprime htargetOdd htotal htarget hbudget
  refine ⟨diag, cy, out, hfacts, ?_⟩
  intro gap labels Rm Ra keep Udiag hm ha hgaps hprotect
  have hL : 3 ≤ fwJointRectangleCount n 254 := by
    have hrect := f.hrect
    omega
  have hagree : ∀ z ∈ packedLabelSupport f.hs choice labels, entry out z = entry cy z := by
    intro z hz
    exact (hfacts.2.2.2.2.2.2.2.2.2.2.2.1) z (packed_label_support_subset_rectangle_support f.hs choice labels hz)
  exact packed_prime_diagonal_repair_with_reference_gains f.hs hL hodd choice gap labels Rm Ra
    cy out keep hm ha hgaps hprotect hagree (hfacts.2.2.2.2.2.2.2.2.2.1) (hfacts.2.2.2.2.2.2.2.2.2.2.1)
    (fun r => ((hfacts.2.2.2.2.2.2.2.1) r).2) (fun c => ((hfacts.2.2.2.2.2.2.2.2.1) c).2) target
    ((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue) Udiag D
    (fun i => ⟨hprime i, htargetOdd i, htarget i⟩)

end
end Sude
