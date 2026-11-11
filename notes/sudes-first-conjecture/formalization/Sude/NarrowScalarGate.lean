import Sude.BTScalarGate
import Sude.APNarrowIteration

/-! Scalar gates with separate candidate and retained batch sizes. -/
namespace Sude
noncomputable section

/-- A single paid BT7 threshold, an exact linear stock floor and a BT5 budget
at that floor supply the width-preserving numerical data uniformly for every
eligible depleted set and radius. All controller-specific scalar inequalities
remain explicit. -/
theorem bt_narrow_uniform_numeric_data_from_scalar
    (initial : Finset ℕ) (c X r L η ell Ma Mf : ℝ) (initialRadius g Q steps z : ℕ)
    (hX : 0 < X) (hr : 0 < r) (hη : 0 < η) (hell : 0 < ell) (hg : 0 < g)
    (hMf : 0 < Mf) (hMa : Ma ≤ initial.card)
    (hfloor : ∀ j < steps, Mf ≤ Ma - 2 * Q * (j : ℝ))
    (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hbudget : 2 * ((z * Q : ℕ) : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * Mf ^ 2 * g)
    (hpaid : r * X * Real.exp ell /
      ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * Mf) ≤
        (initialRadius : ℝ) - r * X / (2 * η * Mf)) :
    ∀ j < steps, ∀ S : Finset ℕ, S ⊆ initial → S.card + 2 * Q * j = initial.card →
      ∀ R : ℕ, initialRadius ≤ R → (R : ℝ) ≤ X / L →
        Nonempty {d : BTGrowingNumericData S c X r R L η g (z * Q) //
          btLinearWidth (ell * (Nat.totient g : ℝ) / (2 * g)) η Ma r X g Q j R ≤ d.width} := by
  intro j hj S hsub hcard R hR hcap
  let ζ : ℝ := ell * (Nat.totient g : ℝ) / (2 * g)
  let M : ℝ := Ma - 2 * Q * (j : ℝ)
  let width : ℝ := ζ * g * (η * M * R / (r * X) - 1 / 2)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hphi : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.mpr hg
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hMfM : Mf ≤ M := hfloor j hj
  have hM : 0 ≤ M := le_trans hMf.le hMfM
  have hcardR : (S.card : ℝ) + 2 * (Q : ℝ) * (j : ℝ) = initial.card := by
    exact_mod_cast hcard
  have hMcount : M ≤ S.card := by dsimp [M]; linarith
  have hRreal : (initialRadius : ℝ) ≤ R := by exact_mod_cast hR
  have hpaid' : r * X * Real.exp ell / (ζ * η * Mf) ≤
      (R : ℝ) - r * X / (2 * η * Mf) := by
    dsimp [ζ] at hpaid ⊢
    linarith
  have hentry : Real.exp ell ≤ width / g := by
    exact bt_phase_entry ζ η g M Mf R r X ell hζ hη hgR hMf hMfM hr hX hpaid'
  have hsq : Mf ^ 2 ≤ M ^ 2 := by nlinarith
  have hsq' := mul_le_mul_of_nonneg_right hsq (mul_nonneg hε hgR.le)
  have hbudget' : 2 * ((z * Q : ℕ) : ℝ) * r * X ≤
      (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g := by nlinarith
  let data : BTGrowingNumericData S c X r R L η g (z * Q) := {
    M := M
    ell := ell
    width := width
    M_nonneg := hM
    M_le_count := hMcount
    ell_pos := hell
    width_eq := rfl
    phase_start := hentry
    pair_budget := hbudget'
  }
  exact ⟨⟨data, by rfl⟩⟩

/-- The elementary initial phase's positive-width and uniform set gates
follow from a positive shifted starting radius and the same scalar stock and
pair-budget inequalities. -/
theorem ap_narrow_uniform_numeric_data_from_scalar
    (initial : Finset ℕ) (c X r L η Ma Mf : ℝ) (initialRadius g Q steps z : ℕ)
    (hX : 0 < X) (hr : 0 < r) (hη : 0 < η) (hg : 0 < g)
    (hMf : 0 < Mf) (hMa : Ma ≤ initial.card)
    (hfloor : ∀ j < steps, Mf ≤ Ma - 2 * Q * (j : ℝ))
    (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hbudget : 2 * ((z * Q : ℕ) : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * Mf ^ 2 * g)
    (hshift : 0 < (initialRadius : ℝ) - r * X / (2 * η * Mf)) :
    ∀ j < steps, ∀ S : Finset ℕ, S ⊆ initial → S.card + 2 * Q * j = initial.card →
      ∀ R : ℕ, initialRadius ≤ R → (R : ℝ) ≤ X / L →
        Nonempty {d : APGrowingNumericData S c X r R L η g (z * Q) //
          btLinearWidth 1 η Ma r X g Q j R ≤ d.width} := by
  intro j hj S hsub hcard R hR hcap
  let M : ℝ := Ma - 2 * Q * (j : ℝ)
  let width : ℝ := g * (η * M * R / (r * X) - 1 / 2)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hMfM : Mf ≤ M := hfloor j hj
  have hMpos : 0 < M := lt_of_lt_of_le hMf hMfM
  have hM : 0 ≤ M := hMpos.le
  have hcardR : (S.card : ℝ) + 2 * (Q : ℝ) * (j : ℝ) = initial.card := by
    exact_mod_cast hcard
  have hMcount : M ≤ S.card := by dsimp [M]; linarith
  have hRreal : (initialRadius : ℝ) ≤ R := by exact_mod_cast hR
  have hshift' : 0 < (R : ℝ) - r * X / (2 * η * Mf) := by linarith
  have hwidthbound := bt_shifted_width_lower 1 η g M Mf R r X (by norm_num) hη hgR.le hMf hMfM hr hX
  have hwidthpos : 0 < width := by
    have hp : 0 < (1 : ℝ) * η * g * M * ((R : ℝ) - r * X / (2 * η * Mf)) / (r * X) := by positivity
    dsimp [width]
    linarith
  have hsq : Mf ^ 2 ≤ M ^ 2 := by nlinarith
  have hsq' := mul_le_mul_of_nonneg_right hsq (mul_nonneg hε hgR.le)
  have hbudget' : 2 * ((z * Q : ℕ) : ℝ) * r * X ≤
      (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g := by nlinarith
  let data : APGrowingNumericData S c X r R L η g (z * Q) := {
    M := M
    width := width
    M_nonneg := hM
    M_le_count := hMcount
    width_pos := hwidthpos
    width_eq := rfl
    pair_budget := hbudget'
  }
  refine ⟨⟨data, ?_⟩⟩
  dsimp [data, width, M, btLinearWidth]
  simp



end
end Sude
