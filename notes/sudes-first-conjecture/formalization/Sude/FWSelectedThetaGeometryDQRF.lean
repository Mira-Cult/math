import Sude.FWSelectedThetaWitness

/-! Conditional DQ/RF completion for the exact projected theta witness selected
by `fwSelectedThetaWitness`. The analytic inputs remain explicit on that
selected family's ordered square and full physical reservation. The selection
does not retain the omitted theta growth-diagonal invoices, stock/narrowing,
or radius facts, and this does not prove prime lines, a final threshold or an
absolute line bound on a later flow output. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- Actual remaining analytic DQ/RF premises for one supplied family. -/
structure FWThetaFamilyWidenedInputs {n : ℕ}
    {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (bits Dold : ℕ) (ε : ℝ) : Prop where
  epsilon_nonneg : 0 ≤ ε
  odd_order : Odd n
  load : 4 * (12 * (5 + 16 + 3 * (n / 450) + f.stages.length) + 6 * bits + 4) ≤ n
  left_endpoint : 1 ≤ centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue -
    ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n)
  right_endpoint : centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue +
    ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n) ≤ poolMaximum n
  deleted : (apInterval
    (centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue -
      ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n))
    (centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue +
      ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n)) 2 1 ∩
      (fwThetaFamilyFull f).image (entry f.ordered)).card ≤ Dold
  gate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
    (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
      Real.log (poolMaximum n) - (((Dold + (2*n - 1) : ℕ)) : ℝ)

/-- Use the exact selected theta witness, the geometric premises proved for its
family, and the supplied widened DQ/RF inputs to construct one completion and
synchronized reference. Flow conclusions remain conditional on each supplied
bounded flow and absolute line bounds concern the reference. -/
theorem fw_selected_theta_geometry_dqrf_all_line_flows
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (bits Dold : ℕ) (ε : ℝ)
    (gates : let w := fwSelectedThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
      FWThetaFamilyWidenedInputs w.family bits Dold ε) :
    let w := fwSelectedThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let f := w.family
    let p := w.p
    let oldReference := w.oldReference
    let roles := w.roles
    let full := fwThetaFamilyFull f
    let ordered := f.ordered
    let B : ℝ := (poolMaximum n : ℝ) * (23/924 : ℝ) * Real.sqrt (94*Real.log (8*(n : ℝ)+8))
    let W : ℝ := (poolMaximum n : ℝ) * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8))
    let U : ℝ := Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2)
    let V : ℝ := (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
      3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
    ∃ (diagonal completed reference : Cell n ≃ Fin (n*n)),
      (∀ z ∈ full, entry diagonal z = entry ordered z) ∧
      (∀ z ∈ full ∪ unreservedDiagonalCells full, entry completed z = entry diagonal z) ∧
      (∀ z ∈ full, entry completed z = entry ordered z) ∧
      (∀ z ∈ roles, entry reference z = entry oldReference z) ∧
      (∀ z ∉ roles, entry reference z = entry completed z) ∧
      |(mainSum completed : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry ordered z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum completed : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry ordered z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      (∀ i, |(rowSum completed i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry ordered z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      (∀ i, |(columnSum completed i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry ordered z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      2*n ≤ (actualUnusedPool diagonal (full ∪ unreservedDiagonalCells full)).card ∧
      |centralEntriesMean (actualUnusedPool diagonal (full ∪ unreservedDiagonalCells full)) centralPoolValue -
        centralEntriesMean (actualUnusedPool ordered full) centralPoolValue| ≤ 3 * (poolMaximum n : ℝ) / (4*n) ∧
      mainSum completed = mainSum diagonal ∧ antiSum completed = antiSum diagonal ∧
      mainSum reference = mainSum completed ∧ antiSum reference = antiSum completed ∧
      Set.range (entry completed) = pool n ∧ Function.Injective (entry completed) ∧
    (∀ r, |(rowSum reference r : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    (∀ c, |(columnSum reference c : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    (∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∃ b b' : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b j : ℤ) - (columnSum oldReference j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
        (∀ z ∈ packedRectangleSupport f.hs choice, entry b z = entry oldReference z) ∧
        (∀ z ∉ roles, entry b z = entry ordered z) ∧
        roles.image (entry b) = roles.image (entry ordered) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
        (∀ z ∈ roles, entry b' z = entry b z) ∧
        (∀ z ∉ roles, entry b' z = entry completed z) ∧
        (∀ r, (rowSum b' r : ℤ) - (rowSum reference r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b' j : ℤ) - (columnSum reference j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b' = mainSum reference ∧ antiSum b' = antiSum reference ∧
        (∀ z ∈ packedRectangleSupport f.hs choice, entry b' z = entry reference z) ∧
        roles.image (entry b') = roles.image (entry completed) ∧
        Set.range (entry b') = pool n ∧ Function.Injective (entry b')) := by
  classical
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let w := fwSelectedThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  have dq := fw_theta_family_dqrf_inputs (bits := bits) (Dold := Dold) hnlo w.family ε
    gates.epsilon_nonneg gates.odd_order gates.load gates.left_endpoint gates.right_endpoint gates.deleted gates.gate
  exact fw_projected_theta_dqrf_all_line_flows bmor lower upper hnlo hnhi choice
    w.family w.p w.oldReference w.roles w.network bits Dold ε (fwThetaFamilyFull w.family) rfl dq

end
end Sude
