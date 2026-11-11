import Sude.SpareConjugatedFlowOutput
import Sude.FWSparePerturbedTargetRouting

/-! Route supplied prime targets after a supplied spare-supported cell
permutation. The original CY, its flows, the perturbation bounds and the prime
targets are hypotheses; this does not construct them or repair diagonals. -/

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Transport the supplied flow family to the exact permuted reference, then
route the supplied nominal odd-prime target vector. `keep` is preserved
relative to the permuted reference, not the old CY; an arbitrary predicate is
transported only via the explicit `hP` premise. -/
theorem fw_spare_conjugated_nominal_target_routing
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (roles full support keep : Finset (Cell n))
    (σ : Equiv.Perm (Cell n)) (cy : Cell n ≃ Fin (n*n))
    (hsub : support ⊆ full \ roles) (hfix : ∀ z ∉ support, σ z = z)
    (P P' : (Cell n ≃ Fin (n*n)) → Prop) (hP : ∀ b, P b → P' (σ.trans b))
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
    (hrowChange : ∀ r, |(rowSum (σ.trans cy) r : ℝ) - rowSum cy r| ≤ (poolMaximum n : ℝ))
    (hcolChange : ∀ c, |(columnSum (σ.trans cy) c : ℝ) - columnSum cy c| ≤ (poolMaximum n : ℝ))
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
    ∃ out : Cell n ≃ Fin (n*n),
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum (σ.trans cy) ∧ antiSum out = antiSum (σ.trans cy) ∧
      (∀ z ∈ keep, entry out z = entry (σ.trans cy) z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ roles, entry out z = entry (σ.trans cy) z) ∧
      roles.image (entry out) = roles.image (entry (σ.trans cy)) ∧
      full.image (entry out) = full.image (entry (σ.trans cy)) ∧
      actualUnusedPool out full = actualUnusedPool (σ.trans cy) full ∧ P' out := by
  let valid : (Fin 3 × Fin n → ℤ) → Prop := fun flow =>
    ∀ e, -(((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ) ≤ flow e ∧
      flow e ≤ (((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ)
  let delta : (Fin 3 × Fin n → ℤ) → Fin n → ℤ := fun flow i =>
    2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) flow e i
  have hconj := spare_conjugated_supplied_flows roles full support keep σ cy hsub hfix
    valid valid delta delta P P' hP hflows
  let Q : (Cell n ≃ Fin (n*n)) → Prop := fun out =>
    (∀ z ∉ roles, entry out z = entry (σ.trans cy) z) ∧
    roles.image (entry out) = roles.image (entry (σ.trans cy)) ∧
    full.image (entry out) = full.image (entry (σ.trans cy)) ∧
    actualUnusedPool out full = actualUnusedPool (σ.trans cy) full ∧ P' out
  have hflows' : ∀ fr : Fin 3 × Fin n → ℤ, valid fr →
      ∀ fc : Fin 3 × Fin n → ℤ, valid fc →
      ∃ out : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum out r : ℤ) - (rowSum (σ.trans cy) r : ℤ) = delta fr r) ∧
        (∀ c, (columnSum out c : ℤ) - (columnSum (σ.trans cy) c : ℤ) = delta fc c) ∧
        mainSum out = mainSum (σ.trans cy) ∧ antiSum out = antiSum (σ.trans cy) ∧
        (∀ z ∈ keep, entry out z = entry (σ.trans cy) z) ∧
        Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧ Q out := by
    intro fr hfr fc hfc
    obtain ⟨b, hr, hc, hm, ha, hk, hoff, hi, hf, hu, hp, hinj, hq⟩ := hconj fr hfr fc hfc
    exact ⟨b, hr, hc, hm, ha, hk, hp, hinj, hoff, hi, hf, hu, hq⟩
  exact fw_spare_perturbed_nominal_target_routing bmor lower upper hnlo hnhi hodd p
    cy (σ.trans cy) keep Q target hprime htodd htotal htarget hrow hcol hrowChange hcolChange hexp hflows'

end
end Sude
