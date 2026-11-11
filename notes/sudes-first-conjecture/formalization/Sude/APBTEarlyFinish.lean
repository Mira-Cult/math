import Sude.APBTPhase

/-! A phase can finish before the BT entry threshold is reached. -/
namespace Sude
noncomputable section

/-- If the BT entry target lies beyond the final radius target, the ordinary
phase already reaches the final target and no later phase is required. -/
theorem ap_then_bt_or_finish_from_scalar (mv : MVBrunTitchmarsh)
    (initial classes : Finset ℕ) (lo c X r L η ell Ma Mb Mf target : ℝ)
    (radius g Q apSteps btSteps : ℕ)
    (hprimes : ∀ p ∈ initial, Nat.Prime p)
    (hinterval : ∀ p ∈ initial, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ initial, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hc : 0 ≤ c) (hX : 0 < X) (hr : 0 < r) (hL : 0 < L) (hg : 0 < g)
    (hη : 0 < η) (hell : 0 < ell) (hMf : 0 < Mf) (hMa0 : 0 ≤ Ma) (hMb0 : 0 ≤ Mb)
    (hMa : Ma ≤ initial.card) (htarget : 0 < target)
    (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hstart : 0 < radius) (hclasscount : (classes.card : ℝ) ≤ r)
    (hstock : 2 * Q * (apSteps + btSteps) < initial.card)
    (hfloorAP : Mf ≤ Ma - 2 * Q * (apSteps : ℝ))
    (hfloorBT : Mf ≤ Mb - 2 * Q * (btSteps : ℝ))
    (hreserve : Mb + 2 * Q * (apSteps : ℝ) ≤ Ma)
    (hpair : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * Mf ^ 2 * g)
    (hshift : 0 < (radius : ℝ) - r * X / (2 * η * Mf))
    (hcap : target ≤ X / L - r * X / (2 * η * Mf))
    (hbudgetAP : Real.log
      ((r * X * Real.exp ell / ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * Mf)) /
        ((radius : ℝ) - r * X / (2 * η * Mf))) ≤
      (η * g / (r * X)) * ((apSteps : ℝ) * Ma - Q * (apSteps : ℝ) * ((apSteps : ℝ) - 1)) /
        (1 + (η * g / (r * X)) * Ma))
    (hbudgetBT : Real.log (target /
      (r * X * Real.exp ell / ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * Mf))) ≤
      ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * g / (r * X)) *
        ((btSteps : ℝ) * Mb - Q * (btSteps : ℝ) * ((btSteps : ℝ) - 1)) /
          (1 + ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * g / (r * X)) * Mb)) :
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace g Q initial radius final last stages ∧
      stages.length ≤ apSteps + btSteps ∧ final ⊆ initial ∧
      final.card + 2 * Q * stages.length = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      target ≤ (last : ℝ) - r * X / (2 * η * Mf) := by
  let ζ : ℝ := ell * (Nat.totient g : ℝ) / (2 * g)
  let entry : ℝ := r * X * Real.exp ell / (ζ * η * Mf)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hphi : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.mpr hg
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hentry : 0 < entry := by dsimp [entry]; positivity
  by_cases hcapEntry : entry ≤ X / L - r * X / (2 * η * Mf)
  · exact ap_then_bt_from_scalar mv initial classes lo c X r L η ell Ma Mb Mf target
      radius g Q apSteps btSteps hprimes hinterval hclasses hreduced hc hX hr hL hg hη hell
      hMf hMa0 hMb0 hMa htarget hε hstart hclasscount hstock hfloorAP hfloorBT hreserve
      hpair hshift hcapEntry hcap hbudgetAP hbudgetBT
  · have htargetEntry : target ≤ entry := by linarith
    have hlog : Real.log (target / ((radius : ℝ) - r * X / (2 * η * Mf))) ≤
        Real.log (entry / ((radius : ℝ) - r * X / (2 * η * Mf))) := by
      apply Real.log_le_log (div_pos htarget hshift)
      exact div_le_div_of_nonneg_right htargetEntry hshift.le
    have hbudgetAP' : Real.log (target / ((radius : ℝ) - r * X / (2 * η * Mf))) ≤
        (η * g / (r * X)) * ((apSteps : ℝ) * Ma - Q * (apSteps : ℝ) * ((apSteps : ℝ) - 1)) /
          (1 + (η * g / (r * X)) * Ma) := hlog.trans hbudgetAP
    have hstockAP : 2 * Q * apSteps < initial.card := by
      have hm := Nat.mul_le_mul_left (2 * Q) (show apSteps ≤ apSteps + btSteps by omega)
      omega
    obtain ⟨final, last, stages, htrace, hlen, hsub, hcard, hdisjoint, htarget'⟩ :=
      ap_growing_linear_phase_from_scalar initial classes lo c X r L η Ma Mf target radius g Q apSteps
        hinterval hclasses hc hX hr hL hg hη hMf hMa0 hMa htarget hε hstart hclasscount
        hstockAP hfloorAP hpair hshift hcap hbudgetAP'
    exact ⟨final, last, stages, htrace, by omega, hsub, hcard, hdisjoint, htarget'⟩

end
end Sude
