import Sude.FWProjectedFrozenCYCompletion
import Sude.FWCYReverseSplice
import Sude.FWProjectedCYFlowTransport
import Sude.FWThetaBridgeWideLineScores
import Sude.FWThetaSeedGrowthLineBounds
import Sude.FWCompletedFirstBandAllLineFlows
import Sude.FWSeedNetworkMatching

/-! Apply the frozen CY completion once to a projected family and network.
The exact same resulting square carries the absolute line estimates and the
supplied-flow transport. Prime targets and absolute bounds for later flow
outputs remain separate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- A single supplied projected witness yields a frozen CY completion, line
bounds for that exact completion, and its supplied bounded-flow continuation. -/
theorem fw_projected_frozen_cy_all_line_flows
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles) :
    let full := fwThetaFamilyFull f
    let final := full ∪ unreservedDiagonalCells full
    let ε : ℝ := 4262317/50000000
    let B : ℝ := (poolMaximum n : ℝ) * (23/924 : ℝ) * Real.sqrt (94*Real.log (8*(n : ℝ)+8))
    let W : ℝ := (poolMaximum n : ℝ) * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8))
    let U : ℝ := Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2)
    let V : ℝ := (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
      3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
    ∃ diag cy : Cell n ≃ Fin (n*n),
      (∀ z ∈ full, entry diag z = entry oldReference z) ∧
      (∀ z ∈ final, entry cy z = entry diag z) ∧
      (∀ z ∈ full, entry cy z = entry oldReference z) ∧
      |(mainSum cy : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry oldReference z : ℝ)) +
        ((mainCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤ (poolMaximum n : ℝ) ∧
      |(antiSum cy : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry oldReference z : ℝ)) +
        ((antiCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤ (3/2 : ℝ)*poolMaximum n ∧
      (∀ i, |(rowSum cy i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry oldReference z : ℝ)) +
        ((rowCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*(4262317/50000000 : ℝ))*poolMaximum n) ∧
      (∀ i, |(columnSum cy i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry oldReference z : ℝ)) +
        ((columnCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*(4262317/50000000 : ℝ))*poolMaximum n) ∧
      mainSum cy = mainSum diag ∧ antiSum cy = antiSum diag ∧
      Set.range (entry cy) = pool n ∧ Function.Injective (entry cy) ∧
    (∀ r, |(rowSum cy r : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*0+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    (∀ c, |(columnSum cy c : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*0+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧
        fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
    ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧
        fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
    ∃ b b' : Cell n ≃ Fin (n*n),
      (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
      (∀ c, (columnSum b c : ℤ) - (columnSum oldReference c : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
      mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry b z = entry oldReference z) ∧
      (∀ z ∉ roles, entry b z = entry oldReference z) ∧
      roles.image (entry b) = roles.image (entry oldReference) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
      (∀ z ∈ roles, entry b' z = entry b z) ∧
      (∀ z ∉ roles, entry b' z = entry cy z) ∧
      (∀ r, (rowSum b' r : ℤ) - (rowSum cy r : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
      (∀ c, (columnSum b' c : ℤ) - (columnSum cy c : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
      mainSum b' = mainSum cy ∧ antiSum b' = antiSum cy ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry b' z = entry cy z) ∧
      roles.image (entry b') = roles.image (entry cy) ∧
      Set.range (entry b') = pool n ∧ Function.Injective (entry b') ∧
      (∀ z ∈ unreservedDiagonalCells (fwThetaFamilyFull f), entry b' z = entry cy z) ∧
      (fwThetaFamilyFull f).image (entry b') = (fwThetaFamilyFull f).image (entry cy) ∧
      actualUnusedPool b' (fwThetaFamilyFull f) = actualUnusedPool cy (fwThetaFamilyFull f) := by
  classical
  let B : ℝ := (poolMaximum n : ℝ) * (23/924 : ℝ) * Real.sqrt (94*Real.log (8*(n : ℝ)+8))
  let W : ℝ := (poolMaximum n : ℝ) * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8))
  let U : ℝ := Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2)
  let V : ℝ := (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
    3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
  let ε : ℝ := 4262317/50000000
  let X : ℝ := poolMaximum n
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
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  dsimp only at hgeom
  have hsub : roles ⊆ fwThetaFamilyFull f := by
    rw [net.roles_eq]
    simpa only [fwThetaFamilyFull] using hgeom.2.2.1
  obtain ⟨diag, cy, hdiagfix, hfinalfix, hfullfix, hmain, hanti, hrow, hcol, hmainEq, hantiEq, hpool, hinj⟩ :=
    fw_projected_frozen_cy_completion bmor lower upper hnlo hnhi hodd choice f p oldReference roles net
  let K : ℝ := (4+(7+1/(n : ℝ))*ε)*X
  obtain ⟨completed, hfixed, hactive, hoff, hr, hc⟩ :=
    fw_cy_reverse_splice f.ordered oldReference cy roles (fwThetaFamilyFull f) K
      hsub net.off_roles net.roles_image hfullfix hrow hcol
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0:ℝ) < n := by positivity
  have hdiv : 1/(n:ℝ) ≤ 1 := (div_le_one hnpos).2 hnR
  have hε : 0 ≤ ε := by dsimp [ε]; norm_num
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hsmall : (4+(7+1/(n : ℝ))*ε) ≤ 4+12*ε := by
    have hmul := mul_nonneg (show 0 ≤ 5-1/(n : ℝ) by linarith) hε
    nlinarith
  have hK : K ≤ (1+2*(9*0+6 : ℕ)*ε)*poolMaximum n + 3*poolMaximum n := by
    have h := mul_le_mul_of_nonneg_right hsmall hX
    dsimp [K, X] at h ⊢
    norm_num at h ⊢
    nlinarith
  have hr' := fun r => lt_of_lt_of_le (hr r) hK
  have hc' := fun c => lt_of_lt_of_le (hc c) hK
  have hall := fw_completed_first_band_all_line_flows bmor lower upper hnlo hnhi f.stageCap
    f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
    f.source f.ordered completed oldReference cy (by simpa only [fwThetaFamilyFull] using hfixed)
    ∅ f.batches f.hvalid f.blocks f.hlen f.hdiag f.hord f.hplaced hmatched
    f.πb f.sb f.πw f.sw f.hbridge f.hwideEntry f.hpairgap f.hseedgap
    (f.hrows.rowPairs f.ordered _ net.row_gap) (f.hcols.columnPairs f.ordered _ net.col_gap)
    net.row_network net.col_network
    (fw_packed_row_network_slot f.hrows f.ordered _ net.row_gap)
    (fw_packed_column_network_slot f.hcols f.ordered _ net.col_gap)
    net.row_blocks net.col_blocks roles net.roles_eq net.off_roles net.roles_image hactive hoff net.main_eq net.anti_eq
    net.row_midpoint net.col_midpoint f.gapb f.gapw f.hinvoiceb f.hinvoicew B W U V
    hBW.1 hBW.2.1 hUV.1 hUV.2.2.1 hBW.2.2.1 hBW.2.2.2 hUV.2.1 hUV.2.2.2
    (bits := 0) ε (by simpa only [fwThetaFamilyFull] using hr') (by simpa only [fwThetaFamilyFull] using hc')
    (fwThetaFamilyFull f) rfl (packedRectangleSupport f.hs choice) p ((n/450)*poolMaximum n) net.flows
  have hflow := fw_projected_cy_supplied_flows choice f p oldReference roles net cy hfullfix
  exact ⟨diag, cy, hdiagfix, hfinalfix, hfullfix, hmain, hanti, hrow, hcol, hmainEq, hantiEq, hpool, hinj,
    hall.1, hall.2.1, hflow⟩

end
end Sude
