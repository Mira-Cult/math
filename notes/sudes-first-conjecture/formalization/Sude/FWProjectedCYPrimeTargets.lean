import Sude.FWProjectedFrozenCYAllLineFlows
import Sude.FWCenteredPrimeTargetRouting

/-! Conditional row/column prime targets for the same frozen CY square.
The prime vector and numerical routing budget are supplied; no diagonal
primality or existence of that target vector is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- The exact absolute line radius supplied by the projected frozen CY theorem. -/
def fwFrozenCYLineRadius (n : ℕ) : ℝ :=
  let ε : ℝ := 4262317/50000000
  let B : ℝ := (poolMaximum n : ℝ) * (23/924 : ℝ) * Real.sqrt (94*Real.log (8*(n : ℝ)+8))
  let W : ℝ := (poolMaximum n : ℝ) * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8))
  let U : ℝ := Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2)
  let V : ℝ := (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
    3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
  ((9 : ℝ)/2 + B + W + U + V + (257/250 : ℝ)*poolMaximum n +
    (19033/450 : ℝ)*(201/10000 : ℝ)*poolMaximum n) +
    ((1+2*(9*0+6 : ℕ)*ε)*poolMaximum n + 3*poolMaximum n)

/-- Route a supplied common odd-prime target vector from the exact CY
completion supplied by the projected family and network. -/
theorem fw_projected_cy_prime_targets
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
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
      actualUnusedPool out full = actualUnusedPool cy full := by
  classical
  obtain ⟨diag, cy, hdiagfix, hfinalfix, hfullfix, hmainBound, hantiBound,
    hrowCY, hcolCY, hmainEq, hantiEq, hpoolCY, hinjCY, hrow, hcol, hflows⟩ :=
    fw_projected_frozen_cy_all_line_flows bmor lower upper hnlo (by omega : n ≤ 35733) hodd choice f p oldReference roles net
  let P : (Cell n ≃ Fin (n*n)) → Prop := fun out =>
    (∀ z ∉ roles, entry out z = entry cy z) ∧
    roles.image (entry out) = roles.image (entry cy) ∧
    (∀ z ∈ unreservedDiagonalCells (fwThetaFamilyFull f), entry out z = entry cy z) ∧
    (fwThetaFamilyFull f).image (entry out) = (fwThetaFamilyFull f).image (entry cy) ∧
    actualUnusedPool out (fwThetaFamilyFull f) = actualUnusedPool cy (fwThetaFamilyFull f)
  have hrow' : ∀ i, |(rowSum cy i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n := by
    intro i
    exact le_of_lt (by simpa only [fwFrozenCYLineRadius] using hrow i)
  have hcol' : ∀ i, |(columnSum cy i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n := by
    intro i
    exact le_of_lt (by simpa only [fwFrozenCYLineRadius] using hcol i)
  have hroute := fw_centered_prime_target_of_supplied_flows
    (N := (n/450)*poolMaximum n) hodd p cy (packedRectangleSupport f.hs choice) P target
    (fw_first_band_demand_rounding_threshold lower hnlo) hprime htargetOdd htotal htarget hrow' hcol' hbudget hexp
    (by
      intro fr hfr fc hfc
      obtain ⟨b, out, hr₀, hc₀, hm₀, ha₀, hrect₀, hoff₀, himage₀, hpool₀, hinj₀,
        hactive, hoff, hr, hc, hm, ha, hrect, himage, hpool, hinj, hdiag, hfull, hunused⟩ :=
        hflows fr hfr fc hfc
      exact ⟨out, hr, hc, hm, ha, hrect, hpool, hinj, hoff, himage, hdiag, hfull, hunused⟩)
  obtain ⟨out, hrowPrime, hcolPrime, hmainOut, hantiOut, hrectOut, hpoolOut, hinjOut, hP⟩ := hroute
  exact ⟨diag, cy, out, hdiagfix, hfinalfix, hfullfix, hmainBound, hantiBound, hmainEq, hantiEq,
    hrowPrime, hcolPrime, hmainOut, hantiOut, hrectOut, hpoolOut, hinjOut,
    hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2⟩

end
end Sude
