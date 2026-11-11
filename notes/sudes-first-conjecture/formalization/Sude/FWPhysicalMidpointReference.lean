import Sude.FWRadiusCenteringAny

/-! A physical midpoint reference for the same supplied row network.  The
residual is the original full line less its incident pair endpoints; it
therefore retains all contributions outside this network.  No mean or prime
bound is asserted. -/
namespace Sude
noncomputable section

/-- Original contribution of one oriented physical pair to a line. -/
def physicalPairLineOriginal {n : ℕ} {K : Type*} {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs K a) (k : K) (r : Fin n) : ℤ :=
  (if v.low k = r then (entry a (v.low k, v.column k) : ℤ) else 0) +
  (if v.high k = r then (entry a (v.high k, v.column k) : ℤ) else 0)

/-- Doubled midpoint contribution at the actual incident endpoints. -/
def physicalPairLineMidpointTwice {n : ℕ} {K : Type*} {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs K a) (k : K) (r : Fin n) : ℤ :=
  (if v.low k = r then (entry a (v.low k, v.column k) : ℤ) + entry a (v.high k, v.column k) else 0) +
  (if v.high k = r then (entry a (v.low k, v.column k) : ℤ) + entry a (v.high k, v.column k) else 0)

/-- Midpoint replacement adds the low-to-high signed physical gap. -/
theorem physical_pair_line_midpoint_identity {n : ℕ} {K : Type*}
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a) (k : K) (r : Fin n) :
    physicalPairLineMidpointTwice v k r - 2 * physicalPairLineOriginal v k r =
      rowNetworkDelta v k r := by
  have hg : (entry a (v.high k, v.column k) : ℤ) =
      (entry a (v.low k, v.column k) : ℤ) + v.gap k := by exact_mod_cast v.gap_at k
  unfold physicalPairLineMidpointTwice physicalPairLineOriginal rowNetworkDelta
  split_ifs <;> omega

/-- Twice the full line after replacing each selected physical endpoint by its
pair midpoint. The subtraction retains all other original line contributions. -/
def physicalNetworkMidpointTwice {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a)
    (B : CenteredNetwork E K v) (r : Fin n) : ℤ :=
  2 * (rowSum a r : ℤ) -
    2 * (∑ k ∈ Finset.univ.biUnion B.block, physicalPairLineOriginal v k r) +
    ∑ k ∈ Finset.univ.biUnion B.block, physicalPairLineMidpointTwice v k r

/-- If every radius is the actual sum of its physical gaps, the radius
reference is exactly the original full line with physical midpoints inserted. -/
theorem physical_network_midpoint_identity {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n*n)} (v : RowNetworkPairs K a)
    (B : CenteredNetwork E K v)
    (htotal : ∀ e, ∑ k ∈ B.block e, v.gap k = B.radius e) (r : Fin n) :
    physicalNetworkMidpointTwice v B r = 2 * (rowSum a r : ℤ) +
      ∑ e : E, edgeTransfer B.source B.target (fun e => (B.radius e : ℤ)) e r := by
  classical
  let U := Finset.univ.biUnion B.block
  have hmem : ∀ e, U ∩ B.block e = B.block e := by
    intro e
    apply Finset.inter_eq_right.mpr
    intro k hk
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hk⟩
  have hsum := rowNetwork_sum_by_reservoir v B.block B.source B.target B.disjoint
    B.endpoints U (by intro k hk; exact hk) r
  have heffects : (∑ k ∈ U, rowNetworkDelta v k r) =
      ∑ e : E, edgeTransfer B.source B.target (fun e => (B.radius e : ℤ)) e r := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e he
    have hcast : (∑ k ∈ B.block e, (v.gap k : ℤ)) = (B.radius e : ℤ) := by
      exact_mod_cast htotal e
    simp [hmem e, hcast, edgeTransfer]
  have hpair : (∑ k ∈ U, physicalPairLineMidpointTwice v k r) -
      2 * (∑ k ∈ U, physicalPairLineOriginal v k r) =
      ∑ k ∈ U, rowNetworkDelta v k r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact physical_pair_line_midpoint_identity v k r
  dsimp [physicalNetworkMidpointTwice]
  change 2 * (rowSum a r : ℤ) - 2 * (∑ k ∈ U, physicalPairLineOriginal v k r) +
    (∑ k ∈ U, physicalPairLineMidpointTwice v k r) = _
  rw [← heffects]
  omega

/-- The supplied reference invoice is within 9/2 of the physical midpoint
line, with all other original contributions retained in the reference. -/
theorem physical_network_centered_midpoint_bound {n : ℕ} {K : Type*} [DecidableEq K]
    (p : Fin 3 → Equiv.Perm (Fin n)) {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs K a) (B : CenteredNetwork (Fin 3 × Fin n) K v)
    (htotal : ∀ e, ∑ k ∈ B.block e, v.gap k = B.radius e)
    (hends : ∀ e, B.source e = e.2 ∧ B.target e = p e.1 e.2)
    (centered : Fin n → ℤ)
    (hinvoice : ∀ r, centered r - (rowSum a r : ℤ) =
      ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => p e.1 e.2)
        (fun e => (evenGridCenter (B.radius e) : ℤ)) e r) (r : Fin n) :
    |2 * centered r - physicalNetworkMidpointTwice v B r| ≤ 9 := by
  have hs : B.source = (fun e : Fin 3 × Fin n => e.2) := by
    funext e
    exact (hends e).1
  have ht : B.target = (fun e : Fin 3 × Fin n => p e.1 e.2) := by
    funext e
    exact (hends e).2
  rw [physical_network_midpoint_identity v B htotal r, hs, ht]
  exact fw_three_permutation_centered_invoice_any p B.radius
    (fun r => rowSum a r) centered hinvoice r

end
end Sude
