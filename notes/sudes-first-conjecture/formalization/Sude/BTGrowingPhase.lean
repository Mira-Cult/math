import Sude.BTGrowingWidths

/-! Compose the actual BT phase selection and its target bound. -/
namespace Sude
noncomputable section

/-- Actual BT selection reaches the stated shifted target either by crossing
`X/L` early or by paying the linearly depleted BT9 phase budget. Every
numerical supply, width, stock and budget condition is explicit. -/
theorem mv_growing_linear_phase_reaches_target (mv : MVBrunTitchmarsh)
    (initial classes : Finset ℕ) (lo c X r L η ζ Ma Mf target : ℝ)
    (initialRadius g Q steps : ℕ)
    (hprimes : ∀ p ∈ initial, Nat.Prime p)
    (hinterval : ∀ p ∈ initial, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ initial, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hc : 0 ≤ c) (hX : 0 < X) (hr : 0 < r) (hL : 0 < L) (hg : 0 < g)
    (hη : 0 < η) (hζ : 0 ≤ ζ) (hMf : 0 < Mf) (hMa : 0 ≤ Ma) (htarget : 0 < target)
    (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hstart : 0 < initialRadius) (hclasscount : (classes.card : ℝ) ≤ r)
    (hstock : 2 * Q * steps < initial.card)
    (hM : ∀ j < steps, Mf ≤ Ma - 2 * Q * (j : ℝ))
    (hshift : 0 < (initialRadius : ℝ) - r * X / (2 * η * Mf))
    (hcap : target ≤ X / L - r * X / (2 * η * Mf))
    (hbudget : Real.log (target / ((initialRadius : ℝ) - r * X / (2 * η * Mf))) ≤
      (ζ * η * g / (r * X)) * ((steps : ℝ) * Ma - Q * (steps : ℝ) * ((steps : ℝ) - 1)) /
        (1 + (ζ * η * g / (r * X)) * Ma))
    (hdata : ∀ j < steps, ∀ S : Finset ℕ, S ⊆ initial → S.card + 2 * Q * j = initial.card →
      ∀ R : ℕ, initialRadius ≤ R → (R : ℝ) ≤ X / L →
        Nonempty {d : BTGrowingNumericData S c X r R L η g Q //
          btLinearWidth ζ η Ma r X g Q j R ≤ d.width}) :
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace g Q initial initialRadius final last stages ∧
      BTWidthTrace (btLinearWidth ζ η Ma r X g Q) 0 initialRadius stages ∧
      stages.length ≤ steps ∧ final ⊆ initial ∧
      final.card + 2 * Q * stages.length = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      target ≤ (last : ℝ) - r * X / (2 * η * Mf) := by
  obtain ⟨final, last, stages, htrace, hlen, hstop, hlast, hsub, hcard, hsum, hdisjoint, hwidth⟩ :=
    mv_iterate_growing_interval_stages_with_widths mv initial classes lo c X r L η initialRadius g Q steps
      (btLinearWidth ζ η Ma r X g Q) hprimes hinterval hclasses hreduced hc hX hr hL hg hη.le hε
      hstart hclasscount hstock hdata
  refine ⟨final, last, stages, htrace, hwidth, hlen, hsub, hcard, hdisjoint, ?_⟩
  rcases hstop with hcross | hfull
  · linarith
  · have hM' : ∀ j < stages.length, Mf ≤ Ma - 2 * Q * (j : ℝ) := by
      intro j hj
      exact hM j (by omega)
    have hbudget' : Real.log (target / ((initialRadius : ℝ) - r * X / (2 * η * Mf))) ≤
      (ζ * η * g / (r * X)) *
        ((stages.length : ℝ) * Ma - Q * (stages.length : ℝ) * ((stages.length : ℝ) - 1)) /
          (1 + (ζ * η * g / (r * X)) * Ma) := by simpa [hfull] using hbudget
    exact htrace.linear_width_reaches_target ζ η Ma Mf r X target hwidth hζ hη (by positivity)
      hMf hMa hr hX htarget hM' hshift hbudget'

end
end Sude
