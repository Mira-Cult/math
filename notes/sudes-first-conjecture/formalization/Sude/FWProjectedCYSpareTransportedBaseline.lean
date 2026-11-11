import Sude.FWProjectedCYSpareTargetBaseline
import Sude.SpareCYBaselineTransport

/-! Transport the same completion's baseline bounds through its spare
permutation, preserving all routing outputs. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The transported bounds use the same CY, permutation and reference.
Prime target supply and diagonal-prime repair remain separate. -/
theorem fw_projected_cy_spare_transported_target_baseline
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
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
      |(mainSum cy : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry oldReference z : ℝ)) +
        ((mainCells n \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤ (poolMaximum n : ℝ) ∧
      |(antiSum cy : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry oldReference z : ℝ)) +
        ((antiCells n \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤
            (3/2 : ℝ) * (poolMaximum n : ℝ) ∧
      |(mainSum (σ.trans cy) : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry (σ.trans oldReference) z : ℝ)) +
        ((mainCells n \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool (σ.trans oldReference) full) centralPoolValue)| ≤ (poolMaximum n : ℝ) ∧
      |(antiSum (σ.trans cy) : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry (σ.trans oldReference) z : ℝ)) +
        ((antiCells n \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool (σ.trans oldReference) full) centralPoolValue)| ≤
            (3/2 : ℝ) * (poolMaximum n : ℝ) ∧
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
  obtain ⟨cy, σ, out, hfullfix, hmain, hanti, hoff, hroles, hactive, hdiag, hrowChange,
    hcolChange, hfull, hunused, hr, hc, hm, ha, hkeep, hpool, hinj, hout,
    hrolesImage, houtFull, houtUnused⟩ :=
    fw_projected_cy_spare_nominal_target_baseline bmor lower upper hnlo hnhi hodd otherChoice
      f p oldReference roles net hexp target hprime htodd htotal htarget
  have hfix : ∀ z ∉ full, σ z = z := by
    intro z hz
    apply hoff z
    change z ∉ spare
    rw [← hspare]
    exact fun hs => hz (Finset.mem_sdiff.mp hs).1
  obtain ⟨_, hmain', hanti'⟩ := supplied_cy_reservation_perm_diagonal_errors
    full σ cy oldReference (poolMaximum n : ℝ) ((3/2 : ℝ) * (poolMaximum n : ℝ))
    hfix hfullfix hmain hanti
  exact ⟨cy, σ, out, hfullfix, hmain, hanti, hmain', hanti', hoff, hroles, hactive, hdiag,
    hrowChange, hcolChange, hfull, hunused, hr, hc, hm, ha, hkeep, hpool, hinj, hout,
    hrolesImage, houtFull, houtUnused⟩

end
end Sude
