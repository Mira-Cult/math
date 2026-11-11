import Sude.FWThetaProjectedFreshWideWitness
import Sude.FWProjectedCYSpareOriginalActiveOutputGrids

/-! Join the fresh family, its reference/network and its canonical spare route.
The prime target vector is supplied; no diagonal-prime supply is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

/-- A fresh wide projection and the supplied-target spare-grid continuation
coexist on one family, reference, network, and chosen completion. The separately
retained upstream existential does not export links to every one of its binders.
No equality with its earlier row/column networks is claimed. -/
theorem fw_theta_fresh_spare_output_grids
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hseedCount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) :
    let upstream := fw_theta_projected_fresh_wide_witness mv bmor upper lower sharp upperSharp n hnlo hnhi
      otherChoice a seeds hseed hseedPrime hseedCount
    fwRetainedProposition upstream ∧
    ∃ (p : Fin 3 → Equiv.Perm (Fin n))
      (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
      (w : FWThetaRoleValueInputs f seeds)
      (reference : Cell n ≃ Fin (n*n)) (roles : Finset (Cell n))
      (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
        (fwSelectedThetaChoice hnlo otherChoice)
        f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
        f.hrows f.hcols p f.ordered reference roles)
      (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
      (fresh : FWThetaFreshWideProjection f w.intermediate reference),
      Nonempty (FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254)
        (fwSelectedThetaChoice hnlo otherChoice) f) ∧
      let routed := fw_projected_cy_spare_original_active_output_grids bmor lower upper hnlo hnhi hodd
        otherChoice f p reference roles net hexp target hprime htodd htotal htarget fresh.radius_lower
      fwRetainedProposition routed := by
  classical
  dsimp only
  have upstream := fw_theta_projected_fresh_wide_witness mv bmor upper lower sharp upperSharp n hnlo hnhi
    otherChoice a seeds hseed hseedPrime hseedCount
  refine ⟨upstream, ?_⟩
  exact upstream.elim fun p hp =>
    have hexp := hp.2.1
    hp.2.2.elim fun batches hbatches => hbatches.elim fun hvalid hcand0 =>
    hcand0.elim fun candidates hcand1 => hcand1.elim fun hcard hcand2 =>
    hcand2.elim fun kept hcand3 => hcand3.elim fun hsub hcand4 =>
    hcand4.elim fun hkept hcand =>
    hcand.2.elim fun rows hrows0 => hrows0.elim fun cols hcols0 =>
    hcols0.elim fun hr hhr0 => hhr0.elim fun hc hhc0 =>
    hhc0.elim fun sr hsr0 => hsr0.elim fun sc hsc0 =>
    hsc0.elim fun hsr hhsr0 => hhsr0.elim fun hsc hhsc0 =>
    hhsc0.elim fun wr hwr0 => hwr0.elim fun wc hwc0 =>
    hwc0.elim fun hwr hhwr0 => hhwr0.elim fun hwc hhwc0 =>
    hhwc0.elim fun blocks hblocks0 => hblocks0.elim fun hlen hhlen0 =>
    hhlen0.elim fun old hold0 => hold0.elim fun stock hstock0 =>
    hstock0.elim fun last hlast0 => hlast0.elim fun stages hstages0 =>
    hstages0.elim fun trace htrace0 => htrace0.elim fun hoff hhoff0 =>
    hhoff0.elim fun gr hgr0 => hgr0.elim fun gc hgc0 =>
    hgc0.elim fun hgr hhgr0 => hhgr0.elim fun hgc hhgc0 =>
    hhgc0.elim fun grown hgrown =>
    let hg1 := hgrown.2.2.2.2.2.2.2.2.2.2
    hg1.2.2.2.2.2.2.2.2.2.2.elim fun ω hω => hω.elim fun b hb =>
    hb.2.2.2.2.2.2.2.2.2.elim fun πb hπb => hπb.elim fun sb hsb =>
    hsb.elim fun πw hπw => hπw.elim fun sw hsw => hsw.elim fun new hnew =>
    let hn2 := hnew.2.2.2.2.2.2.2.2.2.2
    hn2.2.2.2.2.2.2.2.2.2.2.elim fun T hT => hT.elim fun U hU =>
    hU.elim fun V hV => hV.elim fun τ hτ => hτ.elim fun final hfinal =>
    let hf2 := hfinal.2.2.2.2.2.2.2.2.2.2
    hf2.2.2.2.2.2.2.elim fun hjointrow' hjr => hjr.elim fun hjointcol' hjc =>
    hjc.elim fun hrowGap hrg => hrg.elim fun hcolGap hcg =>
    hcg.elim fun BR hbr => hbr.elim fun BC hbc =>
    hbc.2.2.2.2.elim fun b₀ hb₀ =>
    hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.elim fun f hfw0 => hfw0.elim fun w hfw =>
    let hfw1 := hfw.2.2.2.2.2.2.2.2.2.2
    let hfw2 := hfw1.2.2.2.2.2.2.2.2.2.2
    let hfw3 := hfw2.2.2.2.2.2.2.2.2.2
    hfw3.1.elim fun net =>
    ⟨p, f, w, b₀, _, net, hexp, hfw3.2.2, hfw3.2.1,
      fw_projected_cy_spare_original_active_output_grids bmor lower upper hnlo hnhi hodd
        otherChoice f p b₀ _ net hexp target hprime htodd htotal htarget hfw3.2.2.radius_lower⟩

end
end Sude
