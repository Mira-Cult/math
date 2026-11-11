import Sude.FWProjectedCYSpareDiagonalDifference

/-! The active-role centered term for a spare-supported cell permutation can
be evaluated on the original reference. No bound on that term is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- A permutation supported inside the reservation, and fixed on the roles,
preserves the unused mean and the roles' centered diagonal difference. -/
theorem spare_perm_active_reference_difference {n : ℕ}
    (full spare roles : Finset (Cell n)) (σ : Equiv.Perm (Cell n))
    (a : Cell n ≃ Fin (n*n)) (hsub : spare ⊆ full)
    (hoff : ∀ z ∉ spare, σ z = z) (hroles : ∀ z ∈ roles, σ z = z) :
    let ν := centralEntriesMean (actualUnusedPool a full) centralPoolValue
    let νσ := centralEntriesMean (actualUnusedPool (σ.trans a) full) centralPoolValue
    ((∑ z ∈ mainCells n ∩ roles, ((entry (σ.trans a) z : ℝ) - νσ)) -
      (∑ z ∈ antiCells n ∩ roles, ((entry (σ.trans a) z : ℝ) - νσ))) =
    ((∑ z ∈ mainCells n ∩ roles, ((entry a z : ℝ) - ν)) -
      (∑ z ∈ antiCells n ∩ roles, ((entry a z : ℝ) - ν))) := by
  classical
  dsimp only
  have hu := (off_support_reservation_value_images full spare hsub σ hoff a).2.2
  rw [hu]
  have heq (line : Finset (Cell n)) :
      (∑ z ∈ line ∩ roles, ((entry (σ.trans a) z : ℝ) -
        centralEntriesMean (actualUnusedPool a full) centralPoolValue)) =
      (∑ z ∈ line ∩ roles, ((entry a z : ℝ) -
        centralEntriesMean (actualUnusedPool a full) centralPoolValue)) := by
    apply Finset.sum_congr rfl
    intro z hz
    have hzrole := (Finset.mem_inter.mp hz).2
    simp only [entry, Equiv.trans_apply, hroles z hzrole]
  rw [heq (mainCells n), heq (antiCells n)]

/-- The previous same-witness spare-rebalanced CY bound can use the original
reference and unused mean on its active roles. The full prior continuation is
retained for that exact completion, permutation and routed square. -/
theorem fw_projected_cy_spare_original_active_difference
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
    let prior := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd
      otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
    let cy := Classical.choose prior
    let σ := Classical.choose (Classical.choose_spec prior)
    let facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec prior))
    let ν := centralEntriesMean (actualUnusedPool oldReference (fwThetaFamilyFull f)) centralPoolValue
    fwRetainedProposition facts ∧
      |(mainSum (σ.trans cy) : ℝ) - (antiSum (σ.trans cy) : ℝ)| ≤
        |(∑ z ∈ mainCells n ∩ roles, ((entry oldReference z : ℝ) - ν)) -
          (∑ z ∈ antiCells n ∩ roles, ((entry oldReference z : ℝ) - ν))| +
          (7/2 : ℝ) * (poolMaximum n : ℝ) := by
  classical
  dsimp only
  let prior := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd
    otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
  let cy := Classical.choose prior
  let σ := Classical.choose (Classical.choose_spec prior)
  let facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec prior))
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let full := fwThetaFamilyFull f
  let spare := packedRectangleSupport f.hs choice \ activeRectangleSupport f.hs choice
    (fwActiveRectangleLabels n f.stages.length f.stageCap)
  have h := fw_projected_cy_spare_active_diagonal_difference bmor lower upper hnlo hnhi hodd
    otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
  refine ⟨facts, ?_⟩
  obtain ⟨_, _, _, _, _, hoff, hroles, _⟩ := facts
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  have hspare : full \ roles = spare := by
    rw [net.roles_eq]
    simpa only [full, spare, fwThetaFamilyFull] using hgeom.2.2.2.1
  have hsub : spare ⊆ full := by
    rw [← hspare]
    exact Finset.sdiff_subset
  have hdiff := spare_perm_active_reference_difference full spare roles σ oldReference hsub hoff hroles
  have hbound := h.2
  change |(mainSum (σ.trans cy) : ℝ) - (antiSum (σ.trans cy) : ℝ)| ≤
    |(∑ z ∈ mainCells n ∩ roles, ((entry (σ.trans oldReference) z : ℝ) -
      centralEntriesMean (actualUnusedPool (σ.trans oldReference) full) centralPoolValue)) -
    (∑ z ∈ antiCells n ∩ roles, ((entry (σ.trans oldReference) z : ℝ) -
      centralEntriesMean (actualUnusedPool (σ.trans oldReference) full) centralPoolValue))| +
      (7/2 : ℝ) * (poolMaximum n : ℝ) at hbound
  rw [hdiff] at hbound
  exact hbound

end
end Sude
