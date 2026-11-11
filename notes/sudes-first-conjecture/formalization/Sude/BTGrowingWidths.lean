import Sude.BTGrowingPrefix
import Sude.BTGrowingIteration

/-! Preserve numerical width lower bounds across growing selections. -/
namespace Sude
noncomputable section

/-- Lower bound for every recorded stage at its true index and radius. -/
inductive BTWidthTrace (lower : ℕ → ℕ → ℝ) : ℕ → ℕ → List BTSelectedStage → Prop
  | nil (j R : ℕ) : BTWidthTrace lower j R []
  | cons (j R : ℕ) (stage : BTSelectedStage) (tail : List BTSelectedStage)
      (hwidth : lower j R ≤ stage.minimum)
      (hrest : BTWidthTrace lower (j + 1) (R + stage.gap) tail) :
      BTWidthTrace lower j R (stage :: tail)

/-- Each stage retains the width bound at its exact global index and at the
radius accumulated from preceding actual gaps. -/
theorem BTWidthTrace.prefix {lower : ℕ → ℕ → ℝ} {j R : ℕ} {stages : List BTSelectedStage}
    (trace : BTWidthTrace lower j R stages) :
    ∀ before stage after, stages = before ++ stage :: after →
      lower (j + before.length) (R + (before.map BTSelectedStage.gap).sum) ≤ stage.minimum := by
  induction trace with
  | nil =>
    intro before stage after h
    cases before <;> simp at h
  | cons j R s tail hwidth hrest ih =>
    intro before stage after he
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      rcases he with ⟨rfl, _⟩
      simpa using hwidth
    | cons x before =>
      simp only [List.cons_append, List.cons.injEq] at he
      rcases he with ⟨rfl, he⟩
      have h := ih before stage after he
      simpa [add_assoc, add_comm, add_left_comm] using h

/-- BT width with the exact linearly depleted stock at stage `j`. -/
def btLinearWidth (ζ η Ma r X : ℝ) (g Q : ℕ) (j R : ℕ) : ℝ :=
  ζ * g * (η * (Ma - 2 * Q * j) * R / (r * X) - 1 / 2)

/-- A recorded linear-stock width pays BT8 for the actual stage and its
actual accumulated radius. -/
theorem BTGrowingTrace.linear_width_prefix_growth {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (ζ η Ma Mf r X : ℝ)
    (widths : BTWidthTrace (btLinearWidth ζ η Ma r X g Q) 0 radius stages)
    (before : List BTSelectedStage) (stage : BTSelectedStage) (after : List BTSelectedStage)
    (he : stages = before ++ stage :: after)
    (hζ : 0 ≤ ζ) (hη : 0 < η) (hg : 0 ≤ (g : ℝ)) (hMf : 0 < Mf)
    (hM : Mf ≤ Ma - 2 * Q * (before.length : ℝ)) (hr : 0 < r) (hX : 0 < X) :
    (1 + ζ * η * g * (Ma - 2 * Q * (before.length : ℝ)) / (r * X)) *
      ((radius + (before.map BTSelectedStage.gap).sum : ℕ) - r * X / (2 * η * Mf)) ≤
    ((radius + (before.map BTSelectedStage.gap).sum : ℕ) : ℝ) + stage.gap - r * X / (2 * η * Mf) := by
  have hw := widths.prefix before stage after he
  simp only [Nat.zero_add, btLinearWidth] at hw
  exact trace.prefix_shifted_growth before stage after he ζ η _ Mf r X hζ hη hg hMf hM hr hX hw

/-- Shifted grid radius immediately before stage `j`. -/
def btShiftedRadius (radius : ℕ) (stages : List BTSelectedStage) (shift : ℝ) (j : ℕ) : ℝ :=
  (radius + ((stages.take j).map BTSelectedStage.gap).sum : ℕ) - shift

/-- Retained linear-stock widths give every one-stage inequality needed by
the generic BT9 phase theorem, for the actual selected trace. -/
theorem BTGrowingTrace.linear_width_steps {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (ζ η Ma Mf r X : ℝ)
    (widths : BTWidthTrace (btLinearWidth ζ η Ma r X g Q) 0 radius stages)
    (hζ : 0 ≤ ζ) (hη : 0 < η) (hg : 0 ≤ (g : ℝ)) (hMf : 0 < Mf)
    (hM : ∀ j < stages.length, Mf ≤ Ma - 2 * Q * (j : ℝ)) (hr : 0 < r) (hX : 0 < X) :
    ∀ j < stages.length,
      (1 + (ζ * η * g / (r * X)) * (Ma - 2 * Q * (j : ℝ))) *
        btShiftedRadius radius stages (r * X / (2 * η * Mf)) j ≤
        btShiftedRadius radius stages (r * X / (2 * η * Mf)) (j + 1) := by
  intro j hj
  have he : stages = stages.take j ++ stages[j] :: stages.drop (j + 1) := by
    calc
      stages = stages.take j ++ stages.drop j := (List.take_append_drop j stages).symm
      _ = stages.take j ++ stages[j] :: stages.drop (j + 1) := by
        rw [List.cons_getElem_drop_succ (l := stages) (n := j) (h := hj)]
  have hbound := trace.linear_width_prefix_growth ζ η Ma Mf r X widths
    (stages.take j) stages[j] (stages.drop (j + 1)) he hζ hη hg hMf
      (by simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using hM j hj) hr hX
  have hnext : btShiftedRadius radius stages (r * X / (2 * η * Mf)) (j + 1) =
      btShiftedRadius radius stages (r * X / (2 * η * Mf)) j + (stages[j].gap : ℝ) := by
    unfold btShiftedRadius
    rw [← List.take_concat_get' stages j hj]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero, Nat.cast_add]
    ring
  rw [hnext]
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at hbound
  dsimp [btShiftedRadius]
  convert hbound using 1 <;> ring

/-- A paid BT9 budget reaches the target for the actual growing trace,
provided its recorded widths and the stated stock bounds hold. -/
theorem BTGrowingTrace.linear_width_reaches_target {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (ζ η Ma Mf r X target : ℝ)
    (widths : BTWidthTrace (btLinearWidth ζ η Ma r X g Q) 0 radius stages)
    (hζ : 0 ≤ ζ) (hη : 0 < η) (hg : 0 ≤ (g : ℝ)) (hMf : 0 < Mf)
    (hMa : 0 ≤ Ma) (hr : 0 < r) (hX : 0 < X) (htarget : 0 < target)
    (hM : ∀ j < stages.length, Mf ≤ Ma - 2 * Q * (j : ℝ))
    (hstart : 0 < (radius : ℝ) - r * X / (2 * η * Mf))
    (hbudget : Real.log (target / ((radius : ℝ) - r * X / (2 * η * Mf))) ≤
      (ζ * η * g / (r * X)) *
        ((stages.length : ℝ) * Ma - Q * (stages.length : ℝ) * ((stages.length : ℝ) - 1)) /
          (1 + (ζ * η * g / (r * X)) * Ma)) :
    target ≤ (last : ℝ) - r * X / (2 * η * Mf) := by
  let S := btShiftedRadius radius stages (r * X / (2 * η * Mf))
  have ha : 0 ≤ ζ * η * g / (r * X) := by positivity
  have hS : 0 < S 0 := by simpa [S, btShiftedRadius] using hstart
  have hstock : ∀ j < stages.length, 0 ≤ Ma - 2 * Q * (j : ℝ) := by
    intro j hj
    linarith [hM j hj]
  have hstep := trace.linear_width_steps ζ η Ma Mf r X widths hζ hη hg hMf hM hr hX
  have hb : Real.log (target / S 0) ≤
      (ζ * η * g / (r * X)) *
        ((stages.length : ℝ) * Ma - Q * (stages.length : ℝ) * ((stages.length : ℝ) - 1)) /
          (1 + (ζ * η * g / (r * X)) * Ma) := by
    simpa [S, btShiftedRadius] using hbudget
  have hgoal := bt_linear_phase_reaches_target S stages.length (ζ * η * g / (r * X)) Ma Q target
    hS ha hMa (by positivity) htarget hstock hstep hb
  have hlast : S stages.length = (last : ℝ) - r * X / (2 * η * Mf) := by
    simp [S, btShiftedRadius, trace.final_accounting.2.2]
  simpa [hlast] using hgoal

/-- Grow the actual grid radius until the target `X/L` is crossed or the
stage budget is exhausted. The uniform numeric condition is an explicit
remaining controller obligation, not a trusted analytic input. -/
theorem mv_iterate_growing_interval_stages_with_widths (mv : MVBrunTitchmarsh)
    (initial classes : Finset ℕ) (lo c X r L η : ℝ) (initialRadius g Q steps : ℕ) (widthLower : ℕ → ℕ → ℝ)
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
        Nonempty {d : BTGrowingNumericData S c X r R L η g Q // widthLower j R ≤ d.width}) :
    ∃ (final : Finset ℕ) (lastRadius : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace g Q initial initialRadius final lastRadius stages ∧
      stages.length ≤ steps ∧ ((X / L < lastRadius) ∨ stages.length = steps) ∧
      initialRadius ≤ lastRadius ∧ final ⊆ initial ∧
      final.card + 2 * Q * stages.length = initial.card ∧
      lastRadius = initialRadius + (stages.map BTSelectedStage.gap).sum ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      BTWidthTrace widthLower 0 initialRadius stages := by
  classical
  have loop : ∀ count j : ℕ, j + count = steps → ∀ S : Finset ℕ, S ⊆ initial →
      S.card + 2 * Q * j = initial.card → ∀ R : ℕ, initialRadius ≤ R →
      ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
        BTGrowingTrace g Q S R final last stages ∧ stages.length ≤ count ∧
          ((X / L < last) ∨ stages.length = count) ∧ R ≤ last ∧ BTWidthTrace widthLower j R stages := by
    intro count
    induction count with
    | zero =>
      intro j hj S hsub hcard R hR
      exact ⟨S, R, [], BTGrowingTrace.nil S R, by simp, Or.inr rfl, le_rfl, BTWidthTrace.nil j R⟩
    | succ count ih =>
      intro j hj S hsub hcard R hR
      by_cases hcap : (R : ℝ) ≤ X / L
      · have hjlt : j < steps := by omega
        have hSpos : 0 < S.card := by
          have hjle : j ≤ steps := by omega
          have hmul := Nat.mul_le_mul_left (2 * Q) hjle
          omega
        have hSne : S.Nonempty := Finset.card_pos.mp hSpos
        obtain ⟨⟨data, hwidthLower⟩⟩ := hdata j hjlt S hsub hcard R hR hcap
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
        obtain ⟨final, last, tail, htrace, hlen, hstop, hlast, hwidthTrace⟩ :=
          ih (j + 1) (by omega) (S \ pairFootprint chosen h) hnewsub hnewcard (R + h) (by omega)
        let stage : BTSelectedStage := ⟨h, chosen, data.width⟩
        have htrace' : BTGrowingTrace g Q S R final last (stage :: tail) :=
          BTGrowingTrace.cons S R stage final last tail hh hdiv hbound hwidth hchosen hmatch hfoot htrace
        refine ⟨final, last, stage :: tail, htrace', by simp only [List.length_cons]; omega, ?_, by omega, ?_⟩
        rcases hstop with hcross | hfull
        · exact Or.inl hcross
        · exact Or.inr (by simp only [List.length_cons]; omega)
        · exact BTWidthTrace.cons j R stage tail hwidthLower hwidthTrace
      · exact ⟨S, R, [], BTGrowingTrace.nil S R, by simp, Or.inl (lt_of_not_ge hcap), le_rfl, BTWidthTrace.nil j R⟩
  obtain ⟨final, last, stages, htrace, hlen, hstop, hlast, hwidthTrace⟩ :=
    loop steps 0 (by simp) initial Finset.Subset.rfl (by simp) initialRadius le_rfl
  have hacct := htrace.final_accounting
  exact ⟨final, last, stages, htrace, hlen, hstop, hlast, hacct.1, hacct.2.1, hacct.2.2,
    htrace.pairwise_disjoint, hwidthTrace⟩


end
end Sude
