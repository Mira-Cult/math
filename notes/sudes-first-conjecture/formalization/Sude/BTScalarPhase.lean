import Sude.BTScalarGate

/-! Concrete scalar-to-phase interfaces, with no assumed controller. -/
namespace Sude
noncomputable section

/-- The actual BT phase reaches its target from one endpoint stock check,
one floor pair budget, one paid entry threshold, and one BT9 budget. -/
theorem mv_growing_linear_phase_from_scalar (mv : MVBrunTitchmarsh)
    (initial classes : Finset ℕ) (lo c X r L η ell Ma Mf target : ℝ)
    (initialRadius g Q steps : ℕ)
    (hprimes : ∀ p ∈ initial, Nat.Prime p)
    (hinterval : ∀ p ∈ initial, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ initial, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hc : 0 ≤ c) (hX : 0 < X) (hr : 0 < r) (hL : 0 < L) (hg : 0 < g)
    (hη : 0 < η) (hell : 0 < ell) (hMf : 0 < Mf) (hMa0 : 0 ≤ Ma)
    (hMa : Ma ≤ initial.card) (htarget : 0 < target)
    (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hstart : 0 < initialRadius) (hclasscount : (classes.card : ℝ) ≤ r)
    (hstock : 2 * Q * steps < initial.card)
    (hfloor : Mf ≤ Ma - 2 * Q * (steps : ℝ))
    (hpair : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * Mf ^ 2 * g)
    (hshift : 0 < (initialRadius : ℝ) - r * X / (2 * η * Mf))
    (hcap : target ≤ X / L - r * X / (2 * η * Mf))
    (hpaid : r * X * Real.exp ell /
      ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * Mf) ≤
        (initialRadius : ℝ) - r * X / (2 * η * Mf))
    (hbudget : Real.log (target / ((initialRadius : ℝ) - r * X / (2 * η * Mf))) ≤
      ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * g / (r * X)) *
        ((steps : ℝ) * Ma - Q * (steps : ℝ) * ((steps : ℝ) - 1)) /
          (1 + ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * g / (r * X)) * Ma)) :
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace g Q initial initialRadius final last stages ∧
      stages.length ≤ steps ∧ final ⊆ initial ∧
      final.card + 2 * Q * stages.length = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      target ≤ (last : ℝ) - r * X / (2 * η * Mf) := by
  let ζ : ℝ := ell * (Nat.totient g : ℝ) / (2 * g)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hphi : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.mpr hg
  have hζ : 0 ≤ ζ := by dsimp [ζ]; positivity
  have hfloor' := bt_linear_stock_floor Ma Mf Q steps hfloor
  have hdata := bt_uniform_numeric_data_from_scalar initial c X r L η ell Ma Mf initialRadius g Q steps
    hX hr hη hell hg hMf hMa hfloor' hε hpair hpaid
  obtain ⟨final, last, stages, htrace, _, hlen, hsub, hcard, hdisjoint, htarget'⟩ :=
    mv_growing_linear_phase_reaches_target mv initial classes lo c X r L η ζ Ma Mf target initialRadius g Q steps
      hprimes hinterval hclasses hreduced hc hX hr hL hg hη hζ hMf hMa0 htarget hε hstart
      hclasscount hstock hfloor' hshift hcap hbudget hdata
  exact ⟨final, last, stages, htrace, hlen, hsub, hcard, hdisjoint, htarget'⟩

/-- The initial elementary AP phase reaches its target using only the
corresponding scalar stock, pair and growth budgets. -/
theorem ap_growing_linear_phase_from_scalar
    (initial classes : Finset ℕ) (lo c X r L η Ma Mf target : ℝ)
    (initialRadius g Q steps : ℕ)
    (hinterval : ∀ p ∈ initial, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ initial, p % g ∈ classes)
    (hc : 0 ≤ c) (hX : 0 < X) (hr : 0 < r) (hL : 0 < L) (hg : 0 < g)
    (hη : 0 < η) (hMf : 0 < Mf) (hMa0 : 0 ≤ Ma)
    (hMa : Ma ≤ initial.card) (htarget : 0 < target)
    (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hstart : 0 < initialRadius) (hclasscount : (classes.card : ℝ) ≤ r)
    (hstock : 2 * Q * steps < initial.card)
    (hfloor : Mf ≤ Ma - 2 * Q * (steps : ℝ))
    (hpair : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * Mf ^ 2 * g)
    (hshift : 0 < (initialRadius : ℝ) - r * X / (2 * η * Mf))
    (hcap : target ≤ X / L - r * X / (2 * η * Mf))
    (hbudget : Real.log (target / ((initialRadius : ℝ) - r * X / (2 * η * Mf))) ≤
      (η * g / (r * X)) * ((steps : ℝ) * Ma - Q * (steps : ℝ) * ((steps : ℝ) - 1)) /
        (1 + (η * g / (r * X)) * Ma)) :
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace g Q initial initialRadius final last stages ∧
      stages.length ≤ steps ∧ final ⊆ initial ∧
      final.card + 2 * Q * stages.length = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      target ≤ (last : ℝ) - r * X / (2 * η * Mf) := by
  have hfloor' := bt_linear_stock_floor Ma Mf Q steps hfloor
  have hdata := ap_uniform_numeric_data_from_scalar initial c X r L η Ma Mf initialRadius g Q steps
    hX hr hη hg hMf hMa hfloor' hε hpair hshift
  obtain ⟨final, last, stages, htrace, _, hlen, hsub, hcard, hdisjoint, htarget'⟩ :=
    ap_growing_linear_phase_reaches_target initial classes lo c X r L η 1 Ma Mf target initialRadius g Q steps
      hinterval hclasses hc hX hr hL hg hη (by norm_num) hMf hMa0 htarget hε hstart
      hclasscount hstock hfloor' hshift hcap (by simpa using hbudget) hdata
  exact ⟨final, last, stages, htrace, hlen, hsub, hcard, hdisjoint, htarget'⟩

end
end Sude
