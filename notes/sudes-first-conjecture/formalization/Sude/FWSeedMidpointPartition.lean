import Sude.FWPhysicalMidpointComplement
import Sude.PhysicalLineCenteredIdentity

/-! Exact partition of an original row midpoint reference into the selected
pair cells, the other original row cells, and explicit network corrections.
No concentration or preservation claim for the centered square is made. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- Split an arbitrary selected-cell contribution and an arbitrary selected
subset of network pairs, retaining all other row cells and network corrections.
The network-pair subset is not assumed to coincide with the selected cells. -/
theorem physical_network_midpoint_selected_partition {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a)
    (B : CenteredNetwork E K v) (A : Finset (Cell n)) (T : Finset K)
    (hT : T ⊆ Finset.univ.biUnion B.block) (r : Fin n) :
    let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion B.block
    (physicalNetworkMidpointTwice v B r : ℝ) =
      2 * (∑ c ∈ R ∩ A, (entry a c : ℝ)) +
      2 * (∑ c ∈ R \ A, (entry a c : ℝ)) +
      (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) +
      ∑ k ∈ U \ T, (rowNetworkDelta v k r : ℝ) := by
  classical
  dsimp only
  let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
  let U := Finset.univ.biUnion B.block
  have hpair : (∑ k ∈ U, physicalPairLineMidpointTwice v k r) -
      2 * (∑ k ∈ U, physicalPairLineOriginal v k r) =
      ∑ k ∈ U, rowNetworkDelta v k r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => physical_pair_line_midpoint_identity v k r)
  have hmidZ : physicalNetworkMidpointTwice v B r =
      2 * (rowSum a r : ℤ) + ∑ k ∈ U, rowNetworkDelta v k r := by
    dsimp [physicalNetworkMidpointTwice]
    change 2 * (rowSum a r : ℤ) - 2 * (∑ k ∈ U, physicalPairLineOriginal v k r) +
      (∑ k ∈ U, physicalPairLineMidpointTwice v k r) = _
    omega
  have hmid := congrArg (fun x : ℤ => (x : ℝ)) hmidZ
  push_cast at hmid
  have hrow : (∑ c ∈ R, (entry a c : ℝ)) = (rowSum a r : ℝ) := by
    dsimp only [R]
    rw [Finset.sum_image]
    · simp [rowSum]
    · intro x hx y hy heq
      exact Prod.mk.inj heq |>.2
  have hrowSplit := Finset.sum_inter_add_sum_sdiff R A (fun c => (entry a c : ℝ))
  rw [hrow] at hrowSplit
  have hnetSplit := Finset.sum_sdiff (f := fun k => (rowNetworkDelta v k r : ℝ)) hT
  change (physicalNetworkMidpointTwice v B r : ℝ) =
      2 * (∑ c ∈ R ∩ A, (entry a c : ℝ)) +
      2 * (∑ c ∈ R \ A, (entry a c : ℝ)) +
      (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) +
      ∑ k ∈ U \ T, (rowNetworkDelta v k r : ℝ)
  linarith

/-- On the same original square, substitute the selected pairs' centered
stage sum, stage means and their complete orientation term into the physical
network midpoint reference. The complement still contains all nonselected
cells, including perpendicular-network and rectangle cells when present. -/
theorem physical_network_midpoint_selected_centered {n P Q : ℕ} (hQ : 0 < Q)
    {E K : Type*} [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a)
    (B : CenteredNetwork E K v)
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (weights : Fin n → Fin P → Fin Q → ℝ) (values : Fin P → Fin Q → ℝ)
    (ω : Fin P → Equiv.Perm (Fin Q)) (gap : ℝ)
    (hweight : ∀ r j q, physicalPairLineWeight cells (fun c => c.1 = r) (j,q) = weights r j q)
    (hmid : ∀ j q, (((entry a (cells ((j,q), false)) : ℝ) +
      entry a (cells ((j,q), true))) / 2) = values j (ω j q))
    (hgap : ∀ j q, (entry a (cells ((j,q), true)) : ℝ) -
      entry a (cells ((j,q), false)) = gap)
    (T : Finset K) (hT : T ⊆ Finset.univ.biUnion B.block) (r : Fin n) :
    let A := Finset.univ.image cells
    let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion B.block
    (physicalNetworkMidpointTwice v B r : ℝ) =
      2 * (stageLineCentered (fun _ _ => Finset.univ) weights values r ω +
        (∑ j, ((∑ q, weights r j q) * ((∑ q, values j q) / (Q : ℝ)))) +
        ∑ p, physicalPairLineOrientation cells (fun c => c.1 = r) p * (gap / 2)) +
      2 * (∑ c ∈ R \ A, (entry a c : ℝ)) +
      (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) +
      ∑ k ∈ U \ T, (rowNetworkDelta v k r : ℝ) := by
  classical
  dsimp only
  let A := Finset.univ.image cells
  let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
  have hline : R ∩ A = A.filter (fun c => c.1 = r) := by
    ext c
    cases c with
    | mk i j => simp [R, and_comm, Prod.mk.injEq, eq_comm]
  have hselected := physicalPair_line_sum_eq_centered hQ cells hcells
    (fun (l : Fin n) c => c.1 = l) a weights values ω gap hweight hmid hgap r
  have hp := physical_network_midpoint_selected_partition v B A T hT r
  dsimp only at hp
  rw [hline, hselected] at hp
  exact hp

/-- A side-preserving match between a selected pair and a physical network
pair identifies its network correction with the negative signed orientation
term. No ordering or disjointness beyond the supplied match is inferred. -/
theorem physical_network_matched_pair_delta {n : ℕ} {α K : Type*}
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a)
    (cells : α × Bool → Cell n) (i : α) (k : K) (r : Fin n) (gap : ℝ)
    (hlow : cells (i, false) = (v.low k, v.column k))
    (hhigh : cells (i, true) = (v.high k, v.column k))
    (hgap : (entry a (cells (i, true)) : ℝ) - entry a (cells (i, false)) = gap) :
    (rowNetworkDelta v k r : ℝ) =
      -gap * physicalPairLineOrientation cells (fun c => c.1 = r) i := by
  classical
  have hv : (entry a (v.high k, v.column k) : ℝ) =
      (entry a (v.low k, v.column k) : ℝ) + v.gap k := by
    exact_mod_cast v.gap_at k
  rw [hlow, hhigh] at hgap
  have hg : (v.gap k : ℝ) = gap := by linarith
  unfold rowNetworkDelta physicalPairLineOrientation
  push_cast
  rw [hlow, hhigh]
  rw [hg]
  split_ifs <;> ring

/-- Summing matched corrections is exact, including any multiplicities in the
supplied map. An actual identification with a set of seed slots needs its own
injectivity and coverage proof. -/
theorem physical_network_matched_delta_sum {n : ℕ} {α K : Type*}
    [DecidableEq K] {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a)
    (cells : α × Bool → Cell n) (T : Finset K) (ι : K → α) (r : Fin n) (gap : ℝ)
    (hmatch : ∀ k ∈ T, cells (ι k, false) = (v.low k, v.column k) ∧
      cells (ι k, true) = (v.high k, v.column k))
    (hgap : ∀ k ∈ T, (entry a (cells (ι k, true)) : ℝ) -
      entry a (cells (ι k, false)) = gap) :
    (∑ k ∈ T, (rowNetworkDelta v k r : ℝ)) =
      -gap * ∑ k ∈ T, physicalPairLineOrientation cells (fun c => c.1 = r) (ι k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact physical_network_matched_pair_delta v cells (ι k) k r gap
    (hmatch k hk).1 (hmatch k hk).2 (hgap k hk)

end
end Sude
