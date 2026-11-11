import Sude.FWSuppliedCYSpareTargetRouting
import Sude.FWProjectedFrozenCYAllLineFlows
import Sude.FWSelectedThetaWitness

/-! One supplied theta family and network yield a CY completion, then a
spare-rebalanced square and nominal target routing on that same completion.
Prime target supply and diagonal-prime repair remain separate. -/

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Construct the original CY once from the supplied exact family/network,
rebalance its latent spare cells, and route a supplied target vector through
the resulting square. The diagonal sums are preserved relative to the
rebalanced square; no common diagonal prime is supplied by this theorem. -/
theorem fw_projected_cy_spare_nominal_target_routing
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice)
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let full := fwThetaFamilyFull f
    let spare := packedRectangleSupport f.hs choice \ activeRectangleSupport f.hs choice
      (fwActiveRectangleLabels n f.stages.length f.stageCap)
    ∃ (cy : Cell n ≃ Fin (n*n)) (σ : Equiv.Perm (Cell n)) (out : Cell n ≃ Fin (n*n)),
      (∀ z ∈ full, entry cy z = entry oldReference z) ∧
      (∀ z ∉ spare, σ z = z) ∧
      (∀ z ∈ roles, σ z = z) ∧
      (∀ z ∈ activeRectangleSupport f.hs choice (fwActiveRectangleLabels n f.stages.length f.stageCap), σ z = z) ∧
      |(∑ z ∈ spare ∩ mainCells n, (entry (σ.trans cy) z : ℝ)) -
        (∑ z ∈ spare ∩ antiCells n, (entry (σ.trans cy) z : ℝ))| ≤ (poolMaximum n : ℝ) ∧
      (∀ r, |(rowSum (σ.trans cy) r : ℝ) - rowSum cy r| ≤ (poolMaximum n : ℝ)) ∧
      (∀ c, |(columnSum (σ.trans cy) c : ℝ) - columnSum cy c| ≤ (poolMaximum n : ℝ)) ∧
      full.image (entry (σ.trans cy)) = full.image (entry cy) ∧
      actualUnusedPool (σ.trans cy) full = actualUnusedPool cy full ∧
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum (σ.trans cy) ∧ antiSum out = antiSum (σ.trans cy) ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry (σ.trans cy) z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ roles, entry out z = entry (σ.trans cy) z) ∧
      roles.image (entry out) = roles.image (entry (σ.trans cy)) ∧
      full.image (entry out) = full.image (entry cy) ∧
      actualUnusedPool out full = actualUnusedPool cy full := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let full := fwThetaFamilyFull f
  let spare := packedRectangleSupport f.hs choice \ activeRectangleSupport f.hs choice
    (fwActiveRectangleLabels n f.stages.length f.stageCap)
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  have hspare : full \ roles = spare := by
    rw [net.roles_eq]
    simpa only [full, spare, fwThetaFamilyFull] using hgeom.2.2.2.1
  obtain ⟨diag, cy, hdiagfix, hfinalfix, hfullfix, hmainBound, hantiBound,
    hrowCY, hcolCY, hmainEq, hantiEq, hpoolCY, hinjCY, hrow, hcol, hflows⟩ :=
    fw_projected_frozen_cy_all_line_flows bmor lower upper hnlo hnhi hodd choice f p oldReference roles net
  have hrow' : ∀ i, |(rowSum cy i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n := by
    intro i
    exact le_of_lt (by simpa only [fwFrozenCYLineRadius] using hrow i)
  have hcol' : ∀ i, |(columnSum cy i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n := by
    intro i
    exact le_of_lt (by simpa only [fwFrozenCYLineRadius] using hcol i)
  have hflows' : ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -(((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ) ≤ fr e ∧
        fr e ≤ (((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -(((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ) ≤ fc e ∧
        fc e ≤ (((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum cy r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum cy c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
        mainSum b = mainSum cy ∧ antiSum b = antiSum cy ∧
        (∀ z ∈ packedRectangleSupport f.hs choice, entry b z = entry cy z) ∧
        (∀ z ∉ roles, entry b z = entry cy z) ∧
        roles.image (entry b) = roles.image (entry cy) ∧
        full.image (entry b) = full.image (entry cy) ∧
        actualUnusedPool b full = actualUnusedPool cy full ∧ True := by
    intro fr hfr fc hfc
    obtain ⟨b, out, hr₀, hc₀, hm₀, ha₀, hrect₀, hoff₀, himage₀, hpool₀, hinj₀,
      hactive, hoff, hr, hc, hm, ha, hrect, himage, hpool, hinj, hdiag, hfull, hunused⟩ :=
      hflows fr hfr fc hfc
    exact ⟨out, hr, hc, hm, ha, hrect, hoff, himage, hfull, hunused, trivial⟩
  obtain ⟨σ, out, hoff, hroles, hactive, hdiag, hrowChange, hcolChange, hfull,
    hunused, hr, hc, hm, ha, hkeep, hpool, hinj, hout, hrolesImage, houtFull, houtUnused, _⟩ :=
    fw_supplied_cy_spare_nominal_target_routing bmor lower upper hnlo hnhi hodd f.stageCap f.hs
      otherChoice p roles full (packedRectangleSupport f.hs choice) cy hspare
      (fun _ => True) (fun _ => True) (by intros; trivial) target hprime htodd htotal htarget
      hrow' hcol' hexp hflows'
  exact ⟨cy, σ, out, hfullfix, hoff, hroles, hactive, hdiag, hrowChange, hcolChange,
    hfull, hunused, hr, hc, hm, ha, hkeep, hpool, hinj, hout, hrolesImage, houtFull, houtUnused⟩

end
end Sude
