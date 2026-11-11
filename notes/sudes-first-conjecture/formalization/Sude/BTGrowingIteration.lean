import Sude.BTGrowingTrace
import Sude.BTStageIteration

/-! Repeated BT selection with the published growing grid radius. -/
namespace Sude
noncomputable section

/-- Source numerical conditions for one growing-radius selection, before
any controller-specific arithmetic has been discharged. -/
structure BTGrowingNumericData (unused : Finset ℕ) (c X r R L η : ℝ) (g Q : ℕ) where
  M : ℝ
  ell : ℝ
  width : ℝ
  M_nonneg : 0 ≤ M
  M_le_count : M ≤ unused.card
  ell_pos : 0 < ell
  width_eq : width = (ell * (Nat.totient g : ℝ) / (2 * g)) * g *
    (η * M * R / (r * X) - 1 / 2)
  phase_start : Real.exp ell ≤ width / g
  pair_budget : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g

/-- Grow the actual grid radius until the target `X/L` is crossed or the
stage budget is exhausted. The uniform numeric condition is an explicit
remaining controller obligation, not a trusted analytic input. -/
theorem mv_iterate_growing_interval_stages (mv : MVBrunTitchmarsh)
    (initial classes : Finset ℕ) (lo c X r L η : ℝ) (initialRadius g Q steps : ℕ)
    (hprimes : ∀ p ∈ initial, Nat.Prime p)
    (hinterval : ∀ p ∈ initial, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ initial, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hc : 0 ≤ c) (hX : 0 < X) (hr : 0 < r) (hL : 0 < L) (hg : 0 < g)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hstart : 0 < initialRadius) (hclasscount : (classes.card : ℝ) ≤ r)
    (hstock : 2 * Q * steps < initial.card)
    (hdata : ∀ j < steps, ∀ S : Finset ℕ, S ⊆ initial → S.card + 2 * Q * j = initial.card →
      ∀ R : ℕ, initialRadius ≤ R → (R : ℝ) ≤ X / L →
        Nonempty (BTGrowingNumericData S c X r R L η g Q)) :
    ∃ (final : Finset ℕ) (lastRadius : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace g Q initial initialRadius final lastRadius stages ∧
      stages.length ≤ steps ∧ ((X / L < lastRadius) ∨ stages.length = steps) ∧
      initialRadius ≤ lastRadius ∧ final ⊆ initial ∧
      final.card + 2 * Q * stages.length = initial.card ∧
      lastRadius = initialRadius + (stages.map BTSelectedStage.gap).sum ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
  classical
  have loop : ∀ count j : ℕ, j + count = steps → ∀ S : Finset ℕ, S ⊆ initial →
      S.card + 2 * Q * j = initial.card → ∀ R : ℕ, initialRadius ≤ R →
      ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
        BTGrowingTrace g Q S R final last stages ∧ stages.length ≤ count ∧
          ((X / L < last) ∨ stages.length = count) ∧ R ≤ last := by
    intro count
    induction count with
    | zero =>
      intro j hj S hsub hcard R hR
      exact ⟨S, R, [], BTGrowingTrace.nil S R, by simp, Or.inr rfl, le_rfl⟩
    | succ count ih =>
      intro j hj S hsub hcard R hR
      by_cases hcap : (R : ℝ) ≤ X / L
      · have hjlt : j < steps := by omega
        have hSpos : 0 < S.card := by
          have hjle : j ≤ steps := by omega
          have hmul := Nat.mul_le_mul_left (2 * Q) hjle
          omega
        have hSne : S.Nonempty := Finset.card_pos.mp hSpos
        obtain ⟨data⟩ := hdata j hjlt S hsub hcard R hR hcap
        have hRposNat : 0 < R := lt_of_lt_of_le hstart hR
        have hRpos : (0 : ℝ) < R := by exact_mod_cast hRposNat
        have hprimeS : ∀ p ∈ S, Nat.Prime p := fun p hp => hprimes p (hsub hp)
        have hintervalS : ∀ p ∈ S, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X := fun p hp => hinterval p (hsub hp)
        have hclassS : ∀ p ∈ S, p % g ∈ classes := fun p hp => hclasses p (hsub hp)
        obtain ⟨h, chosen, hh, hdiv, hfloor, hwidth, hchosen, hmatch, hfoot, hfootcard, hremaining⟩ :=
          mv_interval_stage_from_source_budget mv S classes lo c X r R L η data.M data.ell data.width g Q
            hSne hprimeS hintervalS hclassS hreduced data.M_nonneg data.M_le_count hc hX hr hRpos hL hg
            data.ell_pos hclasscount hη hε hcap data.width_eq data.phase_start data.pair_budget
        have hbound : h ≤ R := by simpa using hfloor
        have hnewsub : S \ pairFootprint chosen h ⊆ initial := Finset.sdiff_subset.trans hsub
        have hnewcard : (S \ pairFootprint chosen h).card + 2 * Q * (j + 1) = initial.card := by
          simp only [Nat.mul_add, Nat.mul_one]
          omega
        obtain ⟨final, last, tail, htrace, hlen, hstop, hlast⟩ :=
          ih (j + 1) (by omega) (S \ pairFootprint chosen h) hnewsub hnewcard (R + h) (by omega)
        let stage : BTSelectedStage := ⟨h, chosen, data.width⟩
        have htrace' : BTGrowingTrace g Q S R final last (stage :: tail) :=
          BTGrowingTrace.cons S R stage final last tail hh hdiv hbound hwidth hchosen hmatch hfoot htrace
        refine ⟨final, last, stage :: tail, htrace', by simp only [List.length_cons]; omega, ?_, by omega⟩
        rcases hstop with hcross | hfull
        · exact Or.inl hcross
        · exact Or.inr (by simp only [List.length_cons]; omega)
      · exact ⟨S, R, [], BTGrowingTrace.nil S R, by simp, Or.inl (lt_of_not_ge hcap), le_rfl⟩
  obtain ⟨final, last, stages, htrace, hlen, hstop, hlast⟩ :=
    loop steps 0 (by simp) initial Finset.Subset.rfl (by simp) initialRadius le_rfl
  have hacct := htrace.final_accounting
  exact ⟨final, last, stages, htrace, hlen, hstop, hlast, hacct.1, hacct.2.1, hacct.2.2,
    htrace.pairwise_disjoint⟩

end
end Sude
