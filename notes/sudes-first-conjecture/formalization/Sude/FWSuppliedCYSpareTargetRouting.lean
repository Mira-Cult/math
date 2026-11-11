import Sude.FWSuppliedCYSpareRebalance
import Sude.FWSpareConjugatedTargetRouting

/-! Rebalance latent spare diagonal cells of one supplied CY candidate, then
route a supplied nominal target vector against that exact modified candidate.
This does not construct the original CY or its flows, supply targets, prove
diagonal-prime reachability, or identify independent witness choices. -/

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

/-- One supplied CY and its original flow family yield one explicitly
spare-rebalanced CY and a routed square for the same supplied target vector.
The keepout is relative to that rebalanced CY; no old-CY value is promised on
moved spare cells. The arbitrary predicate is carried only through `hP`. -/
theorem fw_supplied_cy_spare_nominal_target_routing
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n Pstage : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (hPstage : Pstage ≤ 238) (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (roles full keep : Finset (Cell n)) (cy : Cell n ≃ Fin (n*n))
    (hspare : full \ roles = packedRectangleSupport hs (fwSelectedThetaChoice hnlo otherChoice) \
      activeRectangleSupport hs (fwSelectedThetaChoice hnlo otherChoice)
        (fwActiveRectangleLabels n Pstage hPstage))
    (P P' : (Cell n ≃ Fin (n*n)) → Prop)
    (hP : ∀ σ : Equiv.Perm (Cell n),
      (∀ z ∉ full \ roles, σ z = z) → ∀ b, P b → P' (σ.trans b))
    (target : Fin n → ℕ)
    (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240)
    (hrow : ∀ r, |(rowSum cy r : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n)
    (hcol : ∀ c, |(columnSum cy c : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n)
    (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (hflows : ∀ fr : Fin 3 × Fin n → ℤ,
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
        (∀ z ∈ keep, entry b z = entry cy z) ∧
        (∀ z ∉ roles, entry b z = entry cy z) ∧
        roles.image (entry b) = roles.image (entry cy) ∧
        full.image (entry b) = full.image (entry cy) ∧
        actualUnusedPool b full = actualUnusedPool cy full ∧ P b) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice
      (fwActiveRectangleLabels n Pstage hPstage)
    ∃ (σ : Equiv.Perm (Cell n)) (out : Cell n ≃ Fin (n*n)),
      (∀ z ∉ spare, σ z = z) ∧
      (∀ z ∈ roles, σ z = z) ∧
      (∀ z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n Pstage hPstage), σ z = z) ∧
      |(∑ z ∈ spare ∩ mainCells n, (entry (σ.trans cy) z : ℝ)) -
        (∑ z ∈ spare ∩ antiCells n, (entry (σ.trans cy) z : ℝ))| ≤ (poolMaximum n : ℝ) ∧
      (∀ r, |(rowSum (σ.trans cy) r : ℝ) - rowSum cy r| ≤ (poolMaximum n : ℝ)) ∧
      (∀ c, |(columnSum (σ.trans cy) c : ℝ) - columnSum cy c| ≤ (poolMaximum n : ℝ)) ∧
      full.image (entry (σ.trans cy)) = full.image (entry cy) ∧
      actualUnusedPool (σ.trans cy) full = actualUnusedPool cy full ∧
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum (σ.trans cy) ∧ antiSum out = antiSum (σ.trans cy) ∧
      (∀ z ∈ keep, entry out z = entry (σ.trans cy) z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ roles, entry out z = entry (σ.trans cy) z) ∧
      roles.image (entry out) = roles.image (entry (σ.trans cy)) ∧
      full.image (entry out) = full.image (entry cy) ∧
      actualUnusedPool out full = actualUnusedPool cy full ∧ P' out := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice
    (fwActiveRectangleLabels n Pstage hPstage)
  have hspare' : full \ roles = spare := hspare
  obtain ⟨σ, hoff, hroles, hfullfix, hactive, hdiag, hrowChange, hcolChange, hfull, hunused⟩ :=
    fw_supplied_cy_spare_rebalance hnlo hPstage hs otherChoice full roles cy hspare
  have hsub : spare ⊆ full \ roles := by rw [hspare']
  have hPσ : ∀ b, P b → P' (σ.trans b) := by
    apply hP σ
    simpa only [hspare'] using hoff
  obtain ⟨out, hr, hc, hm, ha, hk, hp, hi, hOff, hRole, hFull, hUnused, hPred⟩ :=
    fw_spare_conjugated_nominal_target_routing bmor lower upper hnlo hnhi hodd p
      roles full spare keep σ cy hsub hoff P P' hPσ target hprime htodd htotal htarget
      hrow hcol hrowChange hcolChange hexp hflows
  exact ⟨σ, out, hoff, hroles, hactive, hdiag, hrowChange, hcolChange, hfull, hunused,
    hr, hc, hm, ha, hk, hp, hi, hOff, hRole, hFull.trans hfull, hUnused.trans hunused, hPred⟩

end
end Sude
