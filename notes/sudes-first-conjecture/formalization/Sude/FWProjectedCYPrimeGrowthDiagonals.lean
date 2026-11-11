import Sude.FWProjectedCYPrimeTargets
import Sude.FWGrowthCYFlowDiagonalTransfer

/-! On one projected family, route a supplied prime-target vector and retain
its growth-diagonal contribution on the same output. Neither target-vector
existence nor primality of the diagonal sums is inferred. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Conditional prime row/column routing and growth-diagonal transfer on the
same CY completion and final flow output. -/
theorem fw_projected_cy_prime_targets_growth_diagonals
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
        ((n + 8 : ℝ) / (2 * (n + 6))) * ((poolMaximum n : ℝ) / 6) := by
  classical
  obtain ⟨diag, cy, out, hdiagfix, hfinalfix, hfullfix, hmainBound, hantiBound, hmainEq, hantiEq,
    hrowPrime, hcolPrime, hmainOut, hantiOut, hrectOut, hpoolOut, hinjOut,
    hoff, himage, hdiag, hfullImage, hunused⟩ :=
    fw_projected_cy_prime_targets bmor lower upper hnlo hnhi hodd choice f p oldReference roles net
      hexp target D hprime htargetOdd htotal htarget hbudget
  have hgrowth := fw_growth_cy_flow_diagonal_transfer choice f p oldReference roles net g cy out hfullfix hrectOut
  exact ⟨diag, cy, out, hdiagfix, hfinalfix, hfullfix, hmainBound, hantiBound, hmainEq, hantiEq,
    hrowPrime, hcolPrime, hmainOut, hantiOut, hrectOut, hpoolOut, hinjOut,
    hoff, himage, hdiag, hfullImage, hunused, hgrowth⟩

end
end Sude
