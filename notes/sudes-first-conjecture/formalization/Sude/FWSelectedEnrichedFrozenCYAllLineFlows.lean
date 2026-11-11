import Sude.FWSelectedEnrichedThetaWitness
import Sude.FWProjectedFrozenCYAllLineFlows

/-! A frozen CY completion for one selected enriched theta witness. Its family,
network, permutation, reference, growth diagonal and role-input records all
come from that same selection. This selection is not identified with the
previous projected selector. Prime targets and absolute bounds on later flow
outputs remain separate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- Retain the selected theta data while constructing a single CY square that
carries the physical line bounds and the conditional supplied-flow contract. -/
theorem fw_selected_enriched_theta_frozen_cy_all_line_flows
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let w := fwSelectedEnrichedThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let f := w.family
    let p := w.p
    let oldReference := w.oldReference
    let roles := w.roles
    (∀ i v, p i v ≠ v) ∧
    (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
    Nonempty (FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice f) ∧
    Nonempty (FWThetaRoleValueInputs f seeds) ∧
    (
    let full := fwThetaFamilyFull f
    let final := full ∪ unreservedDiagonalCells full
    let ε : ℝ := 4262317/50000000
    let B : ℝ := (poolMaximum n : ℝ) * (23/924 : ℝ) * Real.sqrt (94*Real.log (8*(n : ℝ)+8))
    let W : ℝ := (poolMaximum n : ℝ) * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8))
    let U : ℝ := Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2)
    let V : ℝ := (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
      3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
    ∃ diag cy : Cell n ≃ Fin (n*n),
      (∀ z ∈ full, entry diag z = entry oldReference z) ∧
      (∀ z ∈ final, entry cy z = entry diag z) ∧
      (∀ z ∈ full, entry cy z = entry oldReference z) ∧
      |(mainSum cy : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry oldReference z : ℝ)) +
        ((mainCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤ (poolMaximum n : ℝ) ∧
      |(antiSum cy : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry oldReference z : ℝ)) +
        ((antiCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤ (3/2 : ℝ)*poolMaximum n ∧
      (∀ i, |(rowSum cy i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry oldReference z : ℝ)) +
        ((rowCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*(4262317/50000000 : ℝ))*poolMaximum n) ∧
      (∀ i, |(columnSum cy i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry oldReference z : ℝ)) +
        ((columnCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*(4262317/50000000 : ℝ))*poolMaximum n) ∧
      mainSum cy = mainSum diag ∧ antiSum cy = antiSum diag ∧
      Set.range (entry cy) = pool n ∧ Function.Injective (entry cy) ∧
    (∀ r, |(rowSum cy r : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*0+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    (∀ c, |(columnSum cy c : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*0+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧
        fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
    ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧
        fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
    ∃ b b' : Cell n ≃ Fin (n*n),
      (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
      (∀ c, (columnSum b c : ℤ) - (columnSum oldReference c : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
      mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry b z = entry oldReference z) ∧
      (∀ z ∉ roles, entry b z = entry oldReference z) ∧
      roles.image (entry b) = roles.image (entry oldReference) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
      (∀ z ∈ roles, entry b' z = entry b z) ∧
      (∀ z ∉ roles, entry b' z = entry cy z) ∧
      (∀ r, (rowSum b' r : ℤ) - (rowSum cy r : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
      (∀ c, (columnSum b' c : ℤ) - (columnSum cy c : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
      mainSum b' = mainSum cy ∧ antiSum b' = antiSum cy ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry b' z = entry cy z) ∧
      roles.image (entry b') = roles.image (entry cy) ∧
      Set.range (entry b') = pool n ∧ Function.Injective (entry b') ∧
      (∀ z ∈ unreservedDiagonalCells (fwThetaFamilyFull f), entry b' z = entry cy z) ∧
      (fwThetaFamilyFull f).image (entry b') = (fwThetaFamilyFull f).image (entry cy) ∧
      actualUnusedPool b' (fwThetaFamilyFull f) = actualUnusedPool cy (fwThetaFamilyFull f)
    ) := by
  classical
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let w := fwSelectedEnrichedThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  exact ⟨w.derangement, w.expansion, ⟨w.diagonal⟩, ⟨w.roleInputs⟩,
    fw_projected_frozen_cy_all_line_flows bmor lower upper hnlo hnhi hodd choice
      w.family w.p w.oldReference w.roles w.network⟩

end
end Sude
