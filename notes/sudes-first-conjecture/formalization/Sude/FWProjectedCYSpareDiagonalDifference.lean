import Sude.FWProjectedCYSpareTransportedBaseline
import Sude.FWSelectedSpareDiagonalBound
import Sude.EqualCardCenteredBaseline
import Sude.FWSelectedCapacityCYChoiceGrid

/-! A same-permutation bound that separates the active reservation from a
balanced spare contribution. No active-value bound or interval overlap is
asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The supplied baseline errors and equal-cardinality spare terms yield an
active-reservation difference plus the supplied spare error. -/
theorem centered_baseline_split_spare_error {α : Type*} [DecidableEq α]
    (A B full roles spare : Finset α) (v : α → ℝ) (μ M N E₁ E₂ E₃ : ℝ)
    (hcard : A.card = B.card) (hsub : roles ⊆ full) (hspare : full \ roles = spare)
    (hsparecard : (A ∩ spare).card = (B ∩ spare).card)
    (hM : |M - ((∑ z ∈ A ∩ full, v z) + ((A \ full).card : ℝ)*μ)| ≤ E₁)
    (hN : |N - ((∑ z ∈ B ∩ full, v z) + ((B \ full).card : ℝ)*μ)| ≤ E₂)
    (hsparebound : |(∑ z ∈ A ∩ spare, v z) - (∑ z ∈ B ∩ spare, v z)| ≤ E₃) :
    |M - N| ≤ |(∑ z ∈ A ∩ roles, (v z - μ)) -
      (∑ z ∈ B ∩ roles, (v z - μ))| + E₃ + E₁ + E₂ := by
  classical
  have hdis : Disjoint roles spare := by
    rw [← hspare]
    apply Finset.disjoint_left.mpr
    intro z hz hs
    exact (Finset.mem_sdiff.mp hs).2 hz
  have hfull : roles ∪ spare = full := by
    rw [← hspare]
    exact Finset.union_sdiff_of_subset hsub
  have hsplit (L : Finset α) :
      (∑ z ∈ L ∩ full, (v z - μ)) =
        (∑ z ∈ L ∩ roles, (v z - μ)) + (∑ z ∈ L ∩ spare, (v z - μ)) := by
    rw [← hfull, Finset.inter_union_distrib_left, Finset.sum_union]
    exact (hdis.mono Finset.inter_subset_right Finset.inter_subset_right)
  have hspareeq : (∑ z ∈ A ∩ spare, (v z - μ)) -
      (∑ z ∈ B ∩ spare, (v z - μ)) =
      (∑ z ∈ A ∩ spare, v z) - (∑ z ∈ B ∩ spare, v z) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [hsparecard]
    ring
  have h := equal_card_centered_baseline_error A B full v μ M N E₁ E₂ hcard hM hN
  rw [hsplit A, hsplit B] at h
  have habs := abs_add_le
    ((∑ z ∈ A ∩ roles, (v z - μ)) - (∑ z ∈ B ∩ roles, (v z - μ)))
    ((∑ z ∈ A ∩ spare, (v z - μ)) - (∑ z ∈ B ∩ spare, (v z - μ)))
  rw [hspareeq] at habs
  have hid : (∑ z ∈ A ∩ roles, (v z - μ)) + (∑ z ∈ A ∩ spare, (v z - μ)) -
      ((∑ z ∈ B ∩ roles, (v z - μ)) + (∑ z ∈ B ∩ spare, (v z - μ))) =
      ((∑ z ∈ A ∩ roles, (v z - μ)) - (∑ z ∈ B ∩ roles, (v z - μ))) +
      ((∑ z ∈ A ∩ spare, (v z - μ)) - (∑ z ∈ B ∩ spare, (v z - μ))) := by ring
  rw [hid] at h
  rw [hspareeq] at h
  linarith

/-- The original same-CY routing and balancing facts are retained, and its
actual diagonal difference is controlled by the centered active-role term
plus `7X/2`. This does not bound that active term or construct targets. -/
theorem fw_projected_cy_spare_active_diagonal_difference
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
    let out := Classical.choose (Classical.choose_spec (Classical.choose_spec prior))
    let facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec prior))
    let full := fwThetaFamilyFull f
    let ν := centralEntriesMean (actualUnusedPool (σ.trans oldReference) full) centralPoolValue
    fwRetainedProposition facts ∧
      |(mainSum (σ.trans cy) : ℝ) - (antiSum (σ.trans cy) : ℝ)| ≤
        |(∑ z ∈ mainCells n ∩ roles, ((entry (σ.trans oldReference) z : ℝ) - ν)) -
          (∑ z ∈ antiCells n ∩ roles, ((entry (σ.trans oldReference) z : ℝ) - ν))| +
          (7/2 : ℝ) * (poolMaximum n : ℝ) := by
  classical
  dsimp only
  let prior := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd
    otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
  let cy := Classical.choose prior
  let σ := Classical.choose (Classical.choose_spec prior)
  let out := Classical.choose (Classical.choose_spec (Classical.choose_spec prior))
  let facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec prior))
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let full := fwThetaFamilyFull f
  let spare := packedRectangleSupport f.hs choice \ activeRectangleSupport f.hs choice
    (fwActiveRectangleLabels n f.stages.length f.stageCap)
  let ν := centralEntriesMean (actualUnusedPool (σ.trans oldReference) full) centralPoolValue
  refine ⟨facts, ?_⟩
  obtain ⟨hfullfix, _, _, hmain, hanti, hoff, _, _, hsparebound, _⟩ := facts
  change |(∑ z ∈ spare ∩ mainCells n, (entry (σ.trans cy) z : ℝ)) -
    (∑ z ∈ spare ∩ antiCells n, (entry (σ.trans cy) z : ℝ))| ≤
      (poolMaximum n : ℝ) at hsparebound
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  have hsub : roles ⊆ full := by
    rw [net.roles_eq]
    simpa only [full, fwThetaFamilyFull] using hgeom.2.2.1
  have hspare : full \ roles = spare := by
    rw [net.roles_eq]
    simpa only [full, spare, fwThetaFamilyFull] using hgeom.2.2.2.1
  have hfix : ∀ z ∉ full, σ z = z := by
    intro z hz
    apply hoff z
    change z ∉ spare
    rw [← hspare]
    exact fun hs => hz (Finset.mem_sdiff.mp hs).1
  have himage := off_reservation_perm_image full σ hfix
  have hσfull : ∀ z ∈ full, σ z ∈ full := by
    intro z hz
    rw [← himage]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hspareeq : ∀ z ∈ spare,
      entry (σ.trans cy) z = entry (σ.trans oldReference) z := by
    intro z hz
    have hzfull : z ∈ full := by
      rw [← hspare] at hz
      exact (Finset.mem_sdiff.mp hz).1
    exact hfullfix (σ z) (hσfull z hzfull)
  have hsparebound' :
      |(∑ z ∈ mainCells n ∩ spare, (entry (σ.trans oldReference) z : ℝ)) -
        (∑ z ∈ antiCells n ∩ spare, (entry (σ.trans oldReference) z : ℝ))| ≤
          (poolMaximum n : ℝ) := by
    have hm : (∑ z ∈ mainCells n ∩ spare, (entry (σ.trans cy) z : ℝ)) =
        ∑ z ∈ mainCells n ∩ spare, (entry (σ.trans oldReference) z : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact_mod_cast hspareeq z (Finset.mem_inter.mp hz).2
    have ha : (∑ z ∈ antiCells n ∩ spare, (entry (σ.trans cy) z : ℝ)) =
        ∑ z ∈ antiCells n ∩ spare, (entry (σ.trans oldReference) z : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact_mod_cast hspareeq z (Finset.mem_inter.mp hz).2
    have hbal : |(∑ z ∈ mainCells n ∩ spare, (entry (σ.trans cy) z : ℝ)) -
        (∑ z ∈ antiCells n ∩ spare, (entry (σ.trans cy) z : ℝ))| ≤
          (poolMaximum n : ℝ) := by
      simpa only [Finset.inter_comm spare (mainCells n),
        Finset.inter_comm spare (antiCells n)] using hsparebound
    rw [hm, ha] at hbal
    exact hbal
  have hcards := fw_selected_spare_diagonal_bound hnlo f.stageCap f.hs otherChoice f.ordered
  have hsparecard : (mainCells n ∩ spare).card = (antiCells n ∩ spare).card := by
    rw [Finset.inter_comm, Finset.inter_comm (antiCells n)]
    exact hcards.1.trans hcards.2.1.symm
  have hcard : (mainCells n).card = (antiCells n).card := by simp [mainCells_card, antiCells_card]
  have h := centered_baseline_split_spare_error (mainCells n) (antiCells n) full roles spare
    (fun z => (entry (σ.trans oldReference) z : ℝ)) ν
    (mainSum (σ.trans cy) : ℝ) (antiSum (σ.trans cy) : ℝ)
    (poolMaximum n : ℝ) ((3/2 : ℝ)*(poolMaximum n : ℝ)) (poolMaximum n : ℝ)
    hcard hsub hspare hsparecard hmain hanti hsparebound'
  convert h using 1 <;> ring

end
end Sude
