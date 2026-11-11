import Sude.PhysicalPairLineSum
import Sude.SeedConcentrationPreservation

/-! Exact physical line accounting after pairwise midpoint preservation.
The actual signed gaps remain explicit; no network cancellation is inferred. -/
namespace Sude
noncomputable section

/-- A physical selected-line sum minus its fixed midpoint reference and the
actual signed half-gap invoice equals the centered midpoint score. The
reference may vary between pair labels, and the current gaps may have either
sign. Injectivity ensures that each selected physical cell is counted once. -/
theorem physical_pair_signed_midpoint_invoice {α : Type*} [Fintype α] {n : ℕ}
    (cells : α × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Cell n → Prop) [DecidablePred line]
    (a : Cell n ≃ Fin (n*n)) (mean : α → ℝ) :
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry a c : ℝ)) -
      (∑ i, physicalPairLineWeight cells line i * mean i) -
      (∑ i, physicalPairLineOrientation cells line i *
        (((entry a (cells (i,true)) : ℝ) - entry a (cells (i,false))) / 2)) =
      ∑ i, physicalPairLineWeight cells line i *
        (((((entry a (cells (i,false)) : ℝ) + entry a (cells (i,true))) / 2)) - mean i) := by
  classical
  rw [physicalPair_line_sum_midpoint cells hcells line a, Finset.sum_add_distrib]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

/-- A bound on the centered midpoint score therefore gives exactly the same
bound for the physical selected-cell sum after charging the actual signed
orientation invoice. No fixed positive gap or line cancellation is assumed. -/
theorem physical_pair_signed_midpoint_bound {α Λ : Type*} [Fintype α] {n : ℕ}
    (cells : α × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Λ → Cell n → Prop) [∀ l, DecidablePred (line l)]
    (a : Cell n ≃ Fin (n*n)) (mean : α → ℝ) (B : ℝ)
    (hscore : ∀ l, |∑ i, physicalPairLineWeight cells (line l) i *
      (((((entry a (cells (i,false)) : ℝ) + entry a (cells (i,true))) / 2)) - mean i)| ≤ B) :
    ∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry a c : ℝ)) -
      (∑ i, physicalPairLineWeight cells (line l) i * mean i) -
      (∑ i, physicalPairLineOrientation cells (line l) i *
        (((entry a (cells (i,true)) : ℝ) - entry a (cells (i,false))) / 2))| ≤ B := by
  intro l
  rw [physical_pair_signed_midpoint_invoice cells hcells (line l) a mean]
  exact hscore l


/-- For a seed-family midpoint score centered at the original `grown` stage
means, the corresponding selected-cell invoice uses the current square's
actual signed gaps and exactly the same grown-source reference. -/
theorem seed_signed_midpoint_line_bound {n P Q : ℕ} {Λ : Type*}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Λ → Cell n → Prop) [∀ l, DecidablePred (line l)]
    (grown current : Cell n ≃ Fin (n*n)) (B : ℝ)
    (hscore : ∀ l, |∑ j, ∑ i, physicalPairLineWeight cells (line l) (j,i) *
      (((((entry current (cells ((j,i),false)) : ℝ) + entry current (cells ((j,i),true))) / 2)) -
        ((∑ q, (((entry grown (cells ((j,q),false)) : ℝ) + entry grown (cells ((j,q),true))) / 2)) / (Q : ℝ)))| ≤ B) :
    ∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry current c : ℝ)) -
      seedSourceMidpointReference cells line grown l -
      (∑ i : Fin P × Fin Q, physicalPairLineOrientation cells (line l) i *
        (((entry current (cells (i,true)) : ℝ) - entry current (cells (i,false))) / 2))| ≤ B := by
  classical
  let mean : Fin P × Fin Q → ℝ := fun i =>
    (∑ q, (((entry grown (cells ((i.1,q),false)) : ℝ) + entry grown (cells ((i.1,q),true))) / 2)) / (Q : ℝ)
  have hmean (l : Λ) : (∑ i, physicalPairLineWeight cells (line l) i * mean i) =
      seedSourceMidpointReference cells line grown l := by
    rw [Fintype.sum_prod_type]
    unfold seedSourceMidpointReference
    apply Finset.sum_congr rfl
    intro j _
    change (∑ i, physicalPairLineWeight cells (line l) (j,i) * mean (j,i)) = _
    dsimp only [mean]
    rw [Finset.sum_mul]
  intro l
  have heq := physical_pair_signed_midpoint_invoice cells hcells (line l) current mean
  rw [hmean l] at heq
  rw [heq, Fintype.sum_prod_type]
  exact hscore l

end
end Sude
