import Sude.BTPhaseHandoff

/-! Compose an elementary initial phase with the following BT phase. -/
namespace Sude
noncomputable section

/-- The AP phase pays the BT7 entry threshold; the BT phase then reaches the
final shifted target. Stock and endpoint disjointness are carried through the
actual phase boundary. All scalar inequalities and the published MV theorem
are explicit inputs. -/
theorem ap_then_bt_from_scalar (mv : MVBrunTitchmarsh)
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
    (hcapEntry : r * X * Real.exp ell /
      ((ell * (Nat.totient g : ℝ) / (2 * g)) * η * Mf) ≤ X / L - r * X / (2 * η * Mf))
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
  have hstockAP : 2 * Q * apSteps < initial.card := by
    have hm := Nat.mul_le_mul_left (2 * Q) (show apSteps ≤ apSteps + btSteps by omega)
    omega
  obtain ⟨middle, middleRadius, first, hfirst, hlen, hsub, hcard, _, hpaid⟩ :=
    ap_growing_linear_phase_from_scalar initial classes lo c X r L η Ma Mf entry radius g Q apSteps
      hinterval hclasses hc hX hr hL hg hη hMf hMa0 hMa hentry hε hstart hclasscount
      hstockAP hfloorAP hpair hshift hcapEntry hbudgetAP
  have hMb : Mb ≤ middle.card := by
    have hcardR : (middle.card : ℝ) + 2 * (Q : ℝ) * (first.length : ℝ) = initial.card := by
      exact_mod_cast hcard
    have hlenR : (first.length : ℝ) ≤ apSteps := by exact_mod_cast hlen
    have hm := mul_le_mul_of_nonneg_left hlenR (show 0 ≤ 2 * (Q : ℝ) by positivity)
    linarith
  have hstockBT : 2 * Q * btSteps < middle.card := by
    have hm := Nat.mul_le_mul_left (2 * Q) hlen
    simp only [Nat.mul_add] at hstock
    omega
  have hp : ∀ p ∈ middle, Nat.Prime p := fun p hp => hprimes p (hsub hp)
  have hi : ∀ p ∈ middle, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X := fun p hp => hinterval p (hsub hp)
  have hcl : ∀ p ∈ middle, p % g ∈ classes := fun p hp => hclasses p (hsub hp)
  obtain ⟨final, last, second, htrace, hlen2, hfsub, hfcard, hdisjoint, htarget'⟩ :=
    mv_continue_after_paid_entry mv initial middle classes lo c X r L η ell Mb Mf target radius middleRadius g Q btSteps first
      hfirst hp hi hcl hreduced hc hX hr hL hg hη hell hMf hMb0 hMb htarget hε hclasscount
      hstockBT hfloorBT hpair hcap hpaid hbudgetBT
  refine ⟨final, last, first ++ second, htrace, ?_, hfsub, ?_, hdisjoint, htarget'⟩
  · simp only [List.length_append]
    omega
  · simpa using hfcard

end
end Sude
