import Sude.FWSelectedEnrichedCYPrimeRepairNominal
import Sude.T75TargetRadius

/-! Conditional same-selector composition of the supplied T75 brackets and
controlled grid with the nominal first-band CY repair. This does not supply
prime endpoints, target-window data, or the nested physical repair premises. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Given every T75 endpoint, bracket, complete-grid, congruence, total and
margin premise at the actual nominal center and radius, choose the target list
and apply the selected same-CY repair. The repair itself remains conditional
on its explicitly quantified physical grid, gap, keepout and reference gates. -/
theorem fw_selected_enriched_t75_nominal_repair {α β : Type*} [DecidableEq β]
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let D : ℝ := y / 1240
    ∀ (xs : List α) (freeLo freeHi : α → ℕ) (S : Finset β) (low gap : β → ℕ) (h : ℕ),
    0 ≤ D →
    (∀ x ∈ xs, y - D ≤ (freeLo x : ℝ) ∧ (freeLo x : ℝ) ≤ y ∧
      y ≤ (freeHi x : ℝ) ∧ (freeHi x : ℝ) ≤ y + D) →
    (∀ x ∈ xs, freeLo x % h = freeHi x % h) →
    (∀ x ∈ xs, Nat.Prime (freeLo x) ∧ Nat.Prime (freeHi x)) →
    (∀ i ∈ S, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i)) →
    (∀ i ∈ S, y - D ≤ (low i : ℝ) ∧ ((low i + gap i : ℕ) : ℝ) ≤ y + D) →
    CompleteStepGrid S gap h (∑ i ∈ S, gap i) →
    ((∑ i ∈ S, low i) + (xs.map freeLo).sum) % h = (Lucas.poolTotal n) % h →
    ((Lucas.poolTotal n : ℕ) : ℝ) = ((xs.length : ℝ) + (S.card : ℝ)) * y →
    |((∑ i ∈ S, low i : ℕ) : ℝ) + ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2 - (S.card : ℝ) * y| + D ≤
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2 →
    xs.length + S.card = n → (2 : ℝ) < y - D →
    ∃ values : List ℕ, ∃ chosen : Finset β,
      chosen ⊆ S ∧ List.Forall₂ (fun x v => v = freeLo x ∨ v = freeHi x) xs values ∧
      let targets := values ++ S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)
      ∃ hlen : targets.length = n, ∃ target : Fin n → ℕ,
        (∀ i, target i = targets.get ((finCongr hlen.symm) i)) ∧
        (∑ i, target i) = Lucas.poolTotal n ∧
        (∀ i, Nat.Prime (target i) ∧ Odd (target i) ∧ |(target i : ℝ) - y| ≤ D) ∧
    (
    let w := fwSelectedEnrichedThetaWitness mv bmor upper lower sharp upperSharp
      n hnlo hnhi otherChoice a seeds hseed hseedPrime hcount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let f := w.family
    let p := w.p
    let oldReference := w.oldReference
    let roles := w.roles
    let g := w.diagonal
    (∀ i v, p i v ≠ v) ∧
    (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
    Nonempty (FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice f) ∧
    Nonempty (FWThetaRoleValueInputs f seeds) ∧
    (
    let full := fwThetaFamilyFull f
    let final := full ∪ unreservedDiagonalCells full
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    let μ := fun j => (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6 * (n + 8) : ℕ)
    ∃ diag cy out : Cell n ≃ Fin (n*n),
    (
      (∀ z ∈ full, entry diag z = entry oldReference z) ∧
      (∀ z ∈ final, entry cy z = entry diag z) ∧
      (∀ z ∈ full, entry cy z = entry oldReference z) ∧
      |(mainSum cy : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry oldReference z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum cy : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry oldReference z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      mainSum cy = mainSum diag ∧ antiSum cy = antiSum diag ∧
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum cy ∧ antiSum out = antiSum cy ∧
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧
      (∀ z ∉ roles, entry out z = entry cy z) ∧
      roles.image (entry out) = roles.image (entry cy) ∧
      (∀ z ∈ unreservedDiagonalCells full, entry out z = entry cy z) ∧
      full.image (entry out) = full.image (entry cy) ∧
      actualUnusedPool out full = actualUnusedPool cy full ∧
    (∀ z ∈ fwThetaFamilyFull f, z ∈ mainCells n ∨ z ∈ antiCells n → entry out z = entry f.ordered z) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) =
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) =
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry f.ordered z : ℝ)) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) =
      (∑ j, ∑ q ∈ g.T j, growthStageMidpoint (f.stages.get j) q) - 6 * ∑ j, ((f.stages.get j).gap : ℝ) ∧
    (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) =
      (∑ j, ∑ q ∈ g.U j, growthStageMidpoint (f.stages.get j) q) - 6 * ∑ j, ((f.stages.get j).gap : ℝ) ∧
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry out z : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤ ((poolMaximum n : ℝ) / 6) / 2 ∧
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry out z : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤
        ((n + 8 : ℝ) / (2 * (n + 6))) * ((poolMaximum n : ℝ) / 6)
    ) ∧
    (∀ (gap : Fin (fwJointRectangleCount n 254) → ℕ)
      (labels : Finset (Fin (fwJointRectangleCount n 254))) (Rm Ra : ℕ)
      (keep : Finset (Cell n)) (Udiag : ℝ),
      CompleteEvenGrid (labels.filter fun i => choice i = true) gap Rm →
      CompleteEvenGrid (labels.filter fun i => choice i = false) gap Ra →
      (∀ i ∈ labels,
        entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
          entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) + gap i ∧
        entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
          entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) + gap i) →
      (∀ z ∈ keep, ∀ i ∈ labels,
        z ∉ rectangleCells (RectanglePacking.firstRow f.hs i) (RectanglePacking.secondRow f.hs i)
          (RectanglePacking.firstColumn f.hs choice i) (RectanglePacking.secondColumn f.hs choice i)) →
      ∃ before : Finset (Fin (fwJointRectangleCount n 254)), before ⊆ labels ∧
        let reference := packedTradeSequence f.hs choice cy before.toList
        (mainSum reference : ℤ) - (mainSum cy : ℤ) = evenGridCenter Rm ∧
        (antiSum reference : ℤ) - (antiSum cy : ℤ) = evenGridCenter Ra ∧
        (|(mainSum reference : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ Udiag →
         |(antiSum reference : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ Udiag →
         Udiag + D ≤ (evenGridCenter Rm : ℝ) →
         Udiag + D ≤ (evenGridCenter Ra : ℝ) →
         ∃ (q : ℕ) (result : Cell n ≃ Fin (n*n)),
           Nat.Prime q ∧ (∃ i, q = target i) ∧
           (∀ r, rowSum result r = rowSum out r) ∧
           (∀ c, columnSum result c = columnSum out c) ∧
           mainSum result = q ∧ antiSum result = q ∧ Valid result ∧
           Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
           (∀ z ∈ keep, entry result z = entry out z))) )
    ) := by
  classical
  dsimp only
  intro xs freeLo freeHi S low gap h hD hbracket hclass hfreePrime hcontrolledPrime hwindow
    hgrid hcong htotal hmargin hlen habove
  obtain ⟨values, chosen, hsub, hchoice, htargetsLen, target, hget, hsum, hcert⟩ :=
    t75_conditional_indexed_prime_targets xs freeLo freeHi S low gap h (Lucas.poolTotal n) n
      ((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
      (((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue) / 1240)
      hD hbracket hclass hfreePrime hcontrolledPrime hwindow hgrid hcong htotal hmargin hlen habove
  refine ⟨values, chosen, hsub, hchoice, htargetsLen, target, hget, hsum, hcert, ?_⟩
  exact fw_selected_enriched_theta_cy_prime_diagonal_repair_of_nominal_spread
    mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hseedPrime hcount
    target (((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue) / 1240)
    (fun i => (hcert i).1) (fun i => (hcert i).2.1) hsum (fun i => (hcert i).2.2) rfl

end
end Sude
