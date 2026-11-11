import Sude.ReservedStageSignedCancellation

/-! Exact signed cancellation for supplied stage cells and a full FW-size
reservation, separating role and additional keepout deviations. No line,
mean, target or diagonal bounds are asserted. -/
namespace Sude
noncomputable section

/-- A full reservation with the stated FW cardinality has the exact signed
cancellation below. The stage and role sets, stage means, and all geometric
and cardinality hypotheses are supplied; `q` is an arbitrary natural number
within the stated line-capacity hypothesis. -/
theorem fw_full_reserved_stages_signed_cancellation {n P : ℕ} {I : Type*} [DecidableEq I]
    (hP : P ≤ 238) (a : Cell n ≃ Fin (n * n)) (roles full : Finset (Cell n))
    (stages : Finset I) (cells : I → Finset (Cell n)) (d q : ℕ) (mean : I → ℝ)
    (hdis : Set.PairwiseDisjoint (↑stages : Set I) cells)
    (hcard : ∀ j ∈ stages, (cells j).card = 2 * d * (n + 8))
    (hsum : ∀ j ∈ stages,
      (∑ z ∈ cells j, (entry a z : ℝ)) = (2 * d * (n + 8) : ℕ) * mean j)
    (hstage : stages.biUnion cells ⊆ roles) (hroles : roles ⊆ full)
    (hfullCard : full.card = 12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P))
    (hfull : full.card < n * n)
    (hline : 12 * (5 + 16 + 3 * (n / 450) + P) + q ≤ n) :
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j ∈ stages, (mean j - μ)
    let O : ℝ := (∑ z ∈ roles \ stages.biUnion cells, (entry a z : ℝ)) -
      ((roles \ stages.biUnion cells).card : ℝ) * μ
    let D : ℝ := (∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ) * μ
    let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
    let k : ℝ := (n - 12 * (5 + 16 + 3 * (n / 450) + P) - q : ℕ)
    2 * (d : ℝ) * A + k * (centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ) =
      (2 * (d : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) -
        96 * ((238 : ℝ) - P) - 8 * n) - k * (O + D) / N := by
  classical
  let stageCells := stages.biUnion cells
  have hparts : (roles \ stageCells) ∪ (full \ roles) = full \ stageCells := by
    ext z
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have hh : z ∈ roles → z ∈ full := fun hz => hroles hz
    tauto
  have hdisjoint : Disjoint (roles \ stageCells) (full \ roles) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_sdiff.mp hz).1
  have hother : (∑ z ∈ full \ stageCells, (entry a z : ℝ)) -
      ((full \ stageCells).card : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue =
    ((∑ z ∈ roles \ stageCells, (entry a z : ℝ)) -
      ((roles \ stageCells).card : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue) +
    ((∑ z ∈ full \ roles, (entry a z : ℝ)) -
      ((full \ roles).card : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue) := by
    rw [← hparts, Finset.sum_union hdisjoint, Finset.card_union_of_disjoint hdisjoint]
    push_cast
    ring
  have h := actual_reserved_stages_signed_cancellation a full stages cells d
    (12 * (5 + 16 + 3 * (n / 450) + P)) q (96 * (238 - P)) mean
    hdis hcard hsum (hstage.trans hroles) hfullCard hfull hline
  dsimp only at h ⊢
  change _ = _ at hother
  rw [hother] at h
  have hcast : ((96 * (238 - P) : ℕ) : ℝ) = 96 * ((238 : ℝ) - (P : ℝ)) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hP]
  rw [hcast] at h
  exact h

end
end Sude
