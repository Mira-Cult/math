import Sude.BTStageTrace

/-! Repeated physical BT stages under explicit uniform numerical gates. -/
namespace Sude
noncomputable section

/-- All source numerical inputs for one state, including a lower bound on
the next chosen radius. This is a construction condition to prove, not an
analytic import or an assertion that the stage succeeds. -/
structure BTStageNumericData (unused : Finset ℕ) (c X r R L η lower : ℝ) (g Q : ℕ) where
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
  next_radius_lower : lower ≤ width

/-- Repeated BT stages select actual disjoint entries and evolve the radius
to the chosen gap, provided the displayed numerical data exist uniformly at
every subset of the initial stock with the specified stage size and every
radius in the given interval. No whole-controller correctness is assumed;
the uniform numeric gate is an explicit remaining obligation. -/
theorem mv_iterate_interval_stages (mv : MVBrunTitchmarsh)
    (initial classes : Finset ℕ) (lo c X r initialRadius L η lower : ℝ) (g Q steps : ℕ)
    (hprimes : ∀ p ∈ initial, Nat.Prime p)
    (hinterval : ∀ p ∈ initial, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ initial, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hc : 0 ≤ c) (hX : 0 < X) (hr : 0 < r) (hL : 0 < L) (hg : 0 < g)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hlower : 0 < lower) (hstart : lower ≤ initialRadius) (hradius : initialRadius ≤ X / L)
    (hclasscount : (classes.card : ℝ) ≤ r)
    (hstock : 2 * Q * steps < initial.card)
    (hdata : ∀ j < steps, ∀ S : Finset ℕ, S ⊆ initial → S.card + 2 * Q * j = initial.card →
      ∀ R : ℝ, lower ≤ R → R ≤ initialRadius → Nonempty (BTStageNumericData S c X r R L η lower g Q)) :
    ∃ (final : Finset ℕ) (lastRadius : ℝ) (stages : List BTSelectedStage),
      BTStageTrace g Q initial initialRadius final lastRadius stages ∧
      stages.length = steps ∧ lower ≤ lastRadius ∧ lastRadius ≤ initialRadius ∧
      final ⊆ initial ∧ final.card + 2 * Q * steps = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
  classical
  have loop : ∀ count j : ℕ, j + count = steps → ∀ S : Finset ℕ, S ⊆ initial →
      S.card + 2 * Q * j = initial.card → ∀ R : ℝ, lower ≤ R → R ≤ initialRadius →
      ∃ (final : Finset ℕ) (lastRadius : ℝ) (stages : List BTSelectedStage),
        BTStageTrace g Q S R final lastRadius stages ∧ stages.length = count ∧
          lower ≤ lastRadius ∧ lastRadius ≤ R := by
    intro count
    induction count with
    | zero =>
      intro j hj S hsub hcard R hlow hR
      exact ⟨S, R, [], BTStageTrace.nil S R, rfl, hlow, le_rfl⟩
    | succ count ih =>
      intro j hj S hsub hcard R hlow hR
      have hjlt : j < steps := by omega
      have hSpos : 0 < S.card := by
        have hjle : j ≤ steps := by omega
        have hmul := Nat.mul_le_mul_left (2 * Q) hjle
        omega
      have hSne : S.Nonempty := Finset.card_pos.mp hSpos
      obtain ⟨data⟩ := hdata j hjlt S hsub hcard R hlow hR
      have hRpos : 0 < R := lt_of_lt_of_le hlower hlow
      have hRcap : R ≤ X / L := hR.trans hradius
      have hprimeS : ∀ p ∈ S, Nat.Prime p := fun p hp => hprimes p (hsub hp)
      have hintervalS : ∀ p ∈ S, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X := fun p hp => hinterval p (hsub hp)
      have hclassS : ∀ p ∈ S, p % g ∈ classes := fun p hp => hclasses p (hsub hp)
      obtain ⟨h, chosen, hh, hdiv, hfloor, hwidth, hchosen, hmatch, hfoot, hfootcard, hremaining⟩ :=
        mv_interval_stage_from_source_budget mv S classes lo c X r R L η data.M data.ell data.width g Q
          hSne hprimeS hintervalS hclassS hreduced data.M_nonneg data.M_le_count hc hX hr hRpos hL hg
          data.ell_pos hclasscount hη hε hRcap data.width_eq data.phase_start data.pair_budget
      have hnewsub : S \ pairFootprint chosen h ⊆ initial := Finset.sdiff_subset.trans hsub
      have hnewcard : (S \ pairFootprint chosen h).card + 2 * Q * (j + 1) = initial.card := by
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      have hnewlow : lower ≤ (h : ℝ) := data.next_radius_lower.trans hwidth
      have hnewR : (h : ℝ) ≤ R := by
        have hf : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hRpos.le
        have hhR : (h : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hfloor
        exact hhR.trans hf
      obtain ⟨final, lastRadius, tail, htrace, hlen, hlast, hlastR⟩ :=
        ih (j + 1) (by omega) (S \ pairFootprint chosen h) hnewsub hnewcard h hnewlow (hnewR.trans hR)
      let stage : BTSelectedStage := ⟨h, chosen, data.width⟩
      have htrace' : BTStageTrace g Q S R final lastRadius (stage :: tail) :=
        BTStageTrace.cons S R stage final lastRadius tail hh hdiv hnewR hwidth hchosen hmatch hfoot htrace
      exact ⟨final, lastRadius, stage :: tail, htrace', by simp [hlen], hlast, hlastR.trans hnewR⟩
  obtain ⟨final, lastRadius, stages, htrace, hlen, hlow, hlast⟩ :=
    loop steps 0 (by simp) initial Finset.Subset.rfl (by simp) initialRadius hstart le_rfl
  have hcount := htrace.final_subset_and_card
  refine ⟨final, lastRadius, stages, htrace, hlen, hlow, hlast, hcount.1, ?_, htrace.pairwise_disjoint⟩
  simpa only [hlen] using hcount.2

end
end Sude
