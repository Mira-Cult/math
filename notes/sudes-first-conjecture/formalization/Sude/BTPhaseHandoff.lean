import Sude.BTScalarPhase

/-! Carry a paid entry target and physical stock into the BT phase. -/
namespace Sude
noncomputable section

/-- A prior physical trace that has paid the BT7 target can be continued by
an actual BT phase. The logarithmic budget uses the paid lower bound for its
starting shifted radius, so a larger realized starting radius only helps. -/
theorem mv_continue_after_paid_entry (mv : MVBrunTitchmarsh)
    (initial middle classes : Finset ℕ) (lo c X r L η ell Ma Mf target : ℝ)
    (radius middleRadius g Q steps : ℕ) (first : List BTSelectedStage)
    (hfirst : BTGrowingTrace g Q initial radius middle middleRadius first)
    (hprimes : ∀ p ∈ middle, Nat.Prime p)
    (hinterval : ∀ p ∈ middle, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ middle, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hc : 0 ≤ c) (hX : 0 < X) (hr : 0 < r) (hL : 0 < L) (hg : 0 < g)
    (hη : 0 < η) (hell : 0 < ell) (hMf : 0 < Mf) (hMa0 : 0 ≤ Ma)
    (hMa : Ma ≤ middle.card) (htarget : 0 < target)
    (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hclasscount : (classes.card : ℝ) ≤ r) (hstock : 2 * Q * steps < middle.card)
    (hfloor : Mf ≤ Ma - 2 * Q * (steps : ℝ))
    (hpair : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * Mf ^ 2 * g)
    (hcap : target ≤ X / L - r * X / (2 * η * Mf))
    (hpaid : r * X * Real.exp ell /
      ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * Mf) ≤
        (middleRadius : ℝ) - r * X / (2 * η * Mf))
    (hbudget : Real.log (target /
      (r * X * Real.exp ell / ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * Mf))) ≤
      ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * g / (r * X)) *
        ((steps : ℝ) * Ma - Q * (steps : ℝ) * ((steps : ℝ) - 1)) /
          (1 + ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * g / (r * X)) * Ma)) :
    ∃ (final : Finset ℕ) (last : ℕ) (second : List BTSelectedStage),
      BTGrowingTrace g Q initial radius final last (first ++ second) ∧
      second.length ≤ steps ∧ final ⊆ initial ∧
      final.card + 2 * Q * (first.length + second.length) = initial.card ∧
      (first ++ second).Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      target ≤ (last : ℝ) - r * X / (2 * η * Mf) := by
  let ζ : ℝ := ell * (Nat.totient g : ℝ) / (2 * g)
  let entry : ℝ := r * X * Real.exp ell / (ζ * η * Mf)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hphi : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.mpr hg
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hentry : 0 < entry := by dsimp [entry]; positivity
  have hshift : 0 < (middleRadius : ℝ) - r * X / (2 * η * Mf) := lt_of_lt_of_le hentry hpaid
  have hstartR : (0 : ℝ) < middleRadius := by
    have hp : 0 < r * X / (2 * η * Mf) := by positivity
    linarith
  have hstart : 0 < middleRadius := by exact_mod_cast hstartR
  have hratio : target / ((middleRadius : ℝ) - r * X / (2 * η * Mf)) ≤ target / entry :=
    div_le_div_of_nonneg_left htarget.le hentry hpaid
  have hlog : Real.log (target / ((middleRadius : ℝ) - r * X / (2 * η * Mf))) ≤
      Real.log (target / entry) := Real.log_le_log (div_pos htarget hshift) hratio
  have hbudget' : Real.log (target / ((middleRadius : ℝ) - r * X / (2 * η * Mf))) ≤
      ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * g / (r * X)) *
        ((steps : ℝ) * Ma - Q * (steps : ℝ) * ((steps : ℝ) - 1)) /
          (1 + ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * g / (r * X)) * Ma) :=
    hlog.trans hbudget
  obtain ⟨final, last, second, hsecond, hlen, hsub, hcard, hdisjoint, htarget'⟩ :=
    mv_growing_linear_phase_from_scalar mv middle classes lo c X r L η ell Ma Mf target middleRadius g Q steps
      hprimes hinterval hclasses hreduced hc hX hr hL hg hη hell hMf hMa0 hMa htarget hε
      hstart hclasscount hstock hfloor hpair hshift hcap hpaid hbudget'
  have hall := hfirst.append hsecond
  have hacct := hfirst.append_accounting hsecond
  exact ⟨final, last, second, hall, hlen, hacct.1, hacct.2.1, hacct.2.2, htarget'⟩

end
end Sude
