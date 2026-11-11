import Sude.FWThetaFamilyWitness
import Sude.FWThetaNetworkWitness
import Sude.FWFirstBandDQRFInputs
import Sude.FWThetaBridgeWideLineScores
import Sude.FWSeedNetworkMatching

/-! Conditional completion of one supplied projected family/network witness.
All analytic, widened-deletion, occupancy and bounded-flow premises remain
explicit. This does not establish theta extraction, primality, the final
numerical threshold, or an absolute bound on the later flow output. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- Apply DQ/RF to the same supplied ordered square and reference, using the
four-family and network inputs belonging to that square. -/
theorem fw_projected_theta_dqrf_all_line_flows
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (bits Dold : ℕ) (ε : ℝ) (full : Finset (Cell n))
    (hfull : full = packedRectangleSupport f.hs choice ∪
      LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((f.bc ++ f.sc) ++ f.wc) ++ f.gc)))
    (dq : FWFirstBandDQRFInputs n f.stages.length bits Dold (by omega) ε f.ordered full) :
    let ordered := f.ordered
    let B : ℝ := (poolMaximum n : ℝ) * (23/924 : ℝ) * Real.sqrt (94*Real.log (8*(n : ℝ)+8))
    let W : ℝ := (poolMaximum n : ℝ) * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8))
    let U : ℝ := Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2)
    let V : ℝ := (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
      3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
    ∃ (diagonal completed reference : Cell n ≃ Fin (n*n)),
      (∀ z ∈ full, entry diagonal z = entry ordered z) ∧
      (∀ z ∈ full ∪ unreservedDiagonalCells full, entry completed z = entry diagonal z) ∧
      (∀ z ∈ full, entry completed z = entry ordered z) ∧
      (∀ z ∈ roles, entry reference z = entry oldReference z) ∧
      (∀ z ∉ roles, entry reference z = entry completed z) ∧
      |(mainSum completed : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry ordered z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum completed : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry ordered z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      (∀ i, |(rowSum completed i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry ordered z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      (∀ i, |(columnSum completed i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry ordered z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      2*n ≤ (actualUnusedPool diagonal (full ∪ unreservedDiagonalCells full)).card ∧
      |centralEntriesMean (actualUnusedPool diagonal (full ∪ unreservedDiagonalCells full)) centralPoolValue -
        centralEntriesMean (actualUnusedPool ordered full) centralPoolValue| ≤ 3 * (poolMaximum n : ℝ) / (4*n) ∧
      mainSum completed = mainSum diagonal ∧ antiSum completed = antiSum diagonal ∧
      mainSum reference = mainSum completed ∧ antiSum reference = antiSum completed ∧
      Set.range (entry completed) = pool n ∧ Function.Injective (entry completed) ∧
    (∀ r, |(rowSum reference r : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    (∀ c, |(columnSum reference c : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    (∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∃ b b' : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b j : ℤ) - (columnSum oldReference j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
        (∀ z ∈ packedRectangleSupport f.hs choice, entry b z = entry oldReference z) ∧
        (∀ z ∉ roles, entry b z = entry ordered z) ∧
        roles.image (entry b) = roles.image (entry ordered) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
        (∀ z ∈ roles, entry b' z = entry b z) ∧
        (∀ z ∉ roles, entry b' z = entry completed z) ∧
        (∀ r, (rowSum b' r : ℤ) - (rowSum reference r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b' j : ℤ) - (columnSum reference j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b' = mainSum reference ∧ antiSum b' = antiSum reference ∧
        (∀ z ∈ packedRectangleSupport f.hs choice, entry b' z = entry reference z) ∧
        roles.image (entry b') = roles.image (entry completed) ∧
        Set.range (entry b') = pool n ∧ Function.Injective (entry b')) := by
  classical
  let B : ℝ := (poolMaximum n : ℝ) * (23/924 : ℝ) * Real.sqrt (94*Real.log (8*(n : ℝ)+8))
  let W : ℝ := (poolMaximum n : ℝ) * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8))
  let U : ℝ := Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2)
  let V : ℝ := (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
    3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
  have hBW := fw_theta_bridge_wide_line_scores f.hrect f.hwide f.hs choice
    f.br f.bc f.wr f.wc f.hbr f.hbc f.hwr f.hwc f.source f.ordered B W f.hBridgeScore f.hWideScore
  have hUV := fw_theta_seed_growth_line_interfaces f.trace f.hpool f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
    f.grown f.ordered f.ωseed f.τ U V f.hseedPlace f.hseedScore f.hgrowthPlace f.hgrowthRow f.hgrowthCol
  have hmatched : ∀ block ∈ f.blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))) := by
    simpa only [prescribedPoolValues_mean] using f.hmatched
  have h := fw_given_theta_witness_dqrf_all_line_flows bmor lower upper hnlo hnhi f.stageCap
    f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
    f.source f.ordered oldReference ∅ f.batches f.hvalid f.blocks f.hlen f.hdiag f.hord f.hplaced hmatched
    f.πb f.sb f.πw f.sw f.hbridge f.hwideEntry f.hpairgap f.hseedgap
    (f.hrows.rowPairs f.ordered _ net.row_gap) (f.hcols.columnPairs f.ordered _ net.col_gap)
    net.row_network net.col_network
    (fw_packed_row_network_slot f.hrows f.ordered _ net.row_gap)
    (fw_packed_column_network_slot f.hcols f.ordered _ net.col_gap)
    net.row_blocks net.col_blocks roles net.roles_eq net.off_roles net.roles_image net.main_eq net.anti_eq
    net.row_midpoint net.col_midpoint f.gapb f.gapw f.hinvoiceb f.hinvoicew B W U V
    hBW.1 hBW.2.1 hUV.1 hUV.2.2.1 hBW.2.2.1 hBW.2.2.2 hUV.2.1 hUV.2.2.2
    ε full hfull Dold dq.epsilon_nonneg dq.odd_order dq.center_free dq.reserve_capacity dq.load_capacity
    dq.row_lower dq.row_upper dq.column_lower dq.column_upper dq.left_endpoint dq.right_endpoint dq.deleted dq.gate p net.flows
  exact h

end
end Sude
