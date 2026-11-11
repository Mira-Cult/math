import Sude.FWSeedMidpointPartition

/-! Exact cancellation of the matched network orientation from a selected
pair contribution. Other selected pairs and original nonselected cells stay
explicit; this is an identity on the pre-centering square. -/
namespace Sude
noncomputable section
open scoped BigOperators

theorem physical_network_midpoint_seed_cancellation {n P Q : ℕ} (hQ : 0 < Q)
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
    (T : Finset K) (hT : T ⊆ Finset.univ.biUnion B.block)
    (ι : K → Fin P × Fin Q)
    (hmatch : ∀ k ∈ T, cells (ι k, false) = (v.low k, v.column k) ∧
      cells (ι k, true) = (v.high k, v.column k)) (r : Fin n) :
    let A := Finset.univ.image cells
    let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion B.block
    (physicalNetworkMidpointTwice v B r : ℝ) =
      2 * (stageLineCentered (fun _ _ => Finset.univ) weights values r ω +
        (∑ j, ((∑ q, weights r j q) * ((∑ q, values j q) / (Q : ℝ)))) +
        (∑ p, physicalPairLineOrientation cells (fun c => c.1 = r) p * (gap / 2)) -
        (gap / 2) * ∑ k ∈ T, physicalPairLineOrientation cells (fun c => c.1 = r) (ι k)) +
      2 * (∑ c ∈ R \ A, (entry a c : ℝ)) +
      ∑ k ∈ U \ T, (rowNetworkDelta v k r : ℝ) := by
  classical
  dsimp only
  have hp := physical_network_midpoint_selected_centered hQ v B cells hcells weights values
    ω gap hweight hmid hgap T hT r
  dsimp only at hp
  have hd := physical_network_matched_delta_sum v cells T ι r gap hmatch
    (by intro k hk; exact hgap (ι k).1 (ι k).2)
  rw [hd] at hp
  linarith

end
end Sude
