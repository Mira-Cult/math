import Sude.FWPhysicalMidpointReference
namespace Sude
noncomputable section
open scoped BigOperators

/-! The algebraic residual in the physical midpoint reference is exactly
 the contribution of the original line cells outside the supplied network.
 This says nothing about whether those cells remain fixed after other switches. -/

theorem physical_network_line_residual {n : ℕ} {E K : Type*} [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a) (B : CenteredNetwork E K v) (r : Fin n) :
    let U := Finset.univ.biUnion B.block
    let S := (U.product (Finset.univ : Finset Bool)).image (rowNetworkSlot v)
    let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    (rowSum a r : ℤ) - ∑ k ∈ U, physicalPairLineOriginal v k r =
      ∑ c ∈ R \ S, (entry a c : ℤ) := by
  classical
  dsimp only
  let U := Finset.univ.biUnion B.block
  let P := U.product (Finset.univ : Finset Bool)
  let S := P.image (rowNetworkSlot v)
  let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
  change (rowSum a r : ℤ) - ∑ k ∈ U, physicalPairLineOriginal v k r =
    ∑ c ∈ R \ S, (entry a c : ℤ)
  have hpair : (∑ c ∈ S.filter (fun c => c.1 = r), (entry a c : ℤ)) =
      ∑ k ∈ U, physicalPairLineOriginal v k r := by
    rw [Finset.sum_filter]
    dsimp only [S]
    rw [Finset.sum_image ((rowNetworkSlot_injective v).injOn)]
    dsimp only [P]
    change (∑ x ∈ U ×ˢ (Finset.univ : Finset Bool), if (rowNetworkSlot v x).1 = r then (entry a (rowNetworkSlot v x) : ℤ) else 0) = _
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro k hk
    simp [physicalPairLineOriginal, rowNetworkSlot, add_comm]
  have hfilter : S.filter (fun c => c.1 = r) = R ∩ S := by
    ext c
    cases c with
    | mk i j => simp [R, and_comm, Prod.mk.injEq, eq_comm]
  have hrow : (∑ c ∈ R, (entry a c : ℤ)) = rowSum a r := by
    dsimp only [R]
    rw [Finset.sum_image]
    · simp [rowSum]
    · intro x hx y hy heq
      exact Prod.mk.inj heq |>.2
  have hsub : R ∩ S ⊆ R := Finset.inter_subset_left
  have hd := Finset.sum_sdiff (f := fun c => (entry a c : ℤ)) hsub
  rw [hrow] at hd
  rw [hfilter] at hpair
  have hdiff : R \ (R ∩ S) = R \ S := by ext c; simp
  rw [hdiff] at hd
  linarith
/-- The doubled midpoint reference decomposes into original non-network
cells and actual physical pair midpoint contributions. -/
theorem physical_network_midpoint_complement {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a)
    (B : CenteredNetwork E K v) (r : Fin n) :
    let U := Finset.univ.biUnion B.block
    let S := (U.product (Finset.univ : Finset Bool)).image (rowNetworkSlot v)
    let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    physicalNetworkMidpointTwice v B r =
      2 * (∑ c ∈ R \ S, (entry a c : ℤ)) +
        ∑ k ∈ U, physicalPairLineMidpointTwice v k r := by
  classical
  dsimp only
  have h := physical_network_line_residual v B r
  dsimp only at h
  unfold physicalNetworkMidpointTwice
  omega

end
end Sude
