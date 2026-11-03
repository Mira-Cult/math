import Shared.Beeping.Events

/-!
A logical rejection controller. Each application of `R` is one atomic
comparison here. Compiling an executable comparison into finite machine
steps, and proving that it terminates, are separate refinement obligations.
The transition at time zero is the startup beep.
-/
namespace Shared.Beeping.Controller

inductive State where
  | startup
  | testing (candidate test : Nat)
  deriving DecidableEq, Repr

abbrev Comparison := Nat → Nat → Bool

def step (R : Comparison) (e₀ : Nat) : State → State × Bool
  | .startup => (.testing e₀ 0, true)
  | .testing e n =>
      if R e n then (.testing e (n + 1), false)
      else (.testing (e + 1) 0, true)

def system (R : Comparison) (e₀ : Nat) : EventSystem State where
  initial := .startup
  step := step R e₀

def Good (R : Comparison) (e : Nat) : Prop := ∀ n, R e n = true

variable (R : Comparison) (e₀ : Nat)

@[simp] theorem startup_beep : (system R e₀).BeepAt 0 := rfl

@[simp] theorem run_one : (system R e₀).run 1 = .testing e₀ 0 := rfl

theorem run_testing_succ (t : Nat) :
    ∃ e n, (system R e₀).run (t + 1) = .testing e n := by
  induction t with
  | zero => exact ⟨e₀, 0, rfl⟩
  | succ t ih =>
    obtain ⟨e, n, h⟩ := ih
    rw [EventSystem.run_succ, h]
    cases hr : R e n <;> simp [system, step, hr]

theorem success_step {t e n : Nat}
    (hs : (system R e₀).run t = .testing e n) (hr : R e n = true) :
    (system R e₀).run (t + 1) = .testing e (n + 1) := by
  rw [EventSystem.run_succ, hs]
  simp [system, step, hr]

theorem failure_step {t e n : Nat}
    (hs : (system R e₀).run t = .testing e n) (hr : R e n = false) :
    (system R e₀).run (t + 1) = .testing (e + 1) 0 := by
  rw [EventSystem.run_succ, hs]
  simp [system, step, hr]

theorem testing_beep_iff {t e n : Nat}
    (hs : (system R e₀).run t = .testing e n) :
    (system R e₀).BeepAt t ↔ R e n = false := by
  unfold EventSystem.BeepAt
  rw [hs]
  cases h : R e n <;> simp [system, step, h]

theorem tested_prefix (t : Nat) :
    ∀ e n, (system R e₀).run t = .testing e n →
      ∀ i, i < n → R e i = true := by
  induction t with
  | zero => simp [EventSystem.run, system]
  | succ t ih =>
    intro e n hs i hi
    cases hst : (system R e₀).run t with
    | startup =>
      rw [EventSystem.run_succ, hst] at hs
      simp [system, step] at hs
      omega
    | testing e' n' =>
      cases hr : R e' n' with
      | false =>
        have hn := failure_step R e₀ hst hr
        rw [hn] at hs
        cases hs
        omega
      | true =>
        have hn := success_step R e₀ hst hr
        rw [hn] at hs
        have hp := ih e' n' hst
        cases hs
        by_cases hlt : i < n'
        · exact hp i hlt
        · have : i = n' := by omega
          simpa [this] using hr

/-- Once a good candidate is reached, every subsequent transition is silent. -/
theorem good_silent_from {t e n : Nat}
    (hs : (system R e₀).run t = .testing e n) (hg : Good R e) :
    ∀ k, (system R e₀).run (t + k) = .testing e (n + k) := by
  intro k
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have h := success_step R e₀ ih (hg (n + k))
    simpa [Nat.add_assoc] using h

theorem good_implies_silent {t e n : Nat}
    (hs : (system R e₀).run t = .testing e n) (hg : Good R e) :
    (system R e₀).EventuallySilent := by
  refine ⟨t, ?_⟩
  intro s hts
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hts
  have hk := good_silent_from R e₀ hs hg k
  rw [testing_beep_iff R e₀ hk]
  simp [hg (n + k)]

/-- A known failure at test `n + k` forces rejection after finitely many steps,
possibly earlier if an earlier test also fails. -/
theorem failure_reached {t e n k : Nat}
    (hs : (system R e₀).run t = .testing e n) (hf : R e (n + k) = false) :
    ∃ d, (system R e₀).run (t + d) = .testing (e + 1) 0 := by
  induction k generalizing t n with
  | zero =>
    refine ⟨1, ?_⟩
    apply failure_step R e₀ hs
    simpa using hf
  | succ k ih =>
    cases hr : R e n with
    | false => exact ⟨1, failure_step R e₀ hs hr⟩
    | true =>
      have hs' := success_step R e₀ hs hr
      have hf' : R e ((n + 1) + k) = false := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
      obtain ⟨d, hd⟩ := ih hs' hf'
      refine ⟨1 + d, ?_⟩
      simpa [Nat.add_assoc] using hd

/-- Either a candidate is reached, or a good earlier candidate has already
been found. This argument does not decide which candidates are good. -/
theorem reach_or_earlier_good (k : Nat) :
    (∃ t, (system R e₀).run t = .testing (e₀ + k) 0) ∨
    (∃ e, e₀ ≤ e ∧ e < e₀ + k ∧ Good R e) := by
  classical
  induction k with
  | zero => left; exact ⟨1, by simpa using run_one R e₀⟩
  | succ k ih =>
    rcases ih with ⟨t, ht⟩ | ⟨e, hlo, hhi, hg⟩
    · by_cases hg : Good R (e₀ + k)
      · right
        exact ⟨e₀ + k, by omega, by omega, hg⟩
      · have hf : ∃ n, R (e₀ + k) n = false := by
          have hn : ∃ n, R (e₀ + k) n ≠ true := Classical.not_forall.mp hg
          obtain ⟨n, hn⟩ := hn
          refine ⟨n, ?_⟩
          cases hr : R (e₀ + k) n with
          | false => rfl
          | true => exact False.elim (hn hr)
        obtain ⟨n, hn⟩ := hf
        have hn' : R (e₀ + k) (0 + n) = false := by simpa using hn
        obtain ⟨d, hd⟩ := failure_reached R e₀ ht hn'
        left
        exact ⟨t + d, by simpa [Nat.add_assoc] using hd⟩
    · right
      exact ⟨e, hlo, by omega, hg⟩

theorem good_rank_implies_silent (k : Nat) :
    Good R (e₀ + k) → (system R e₀).EventuallySilent := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hg
    rcases reach_or_earlier_good R e₀ k with ⟨t, ht⟩ | ⟨e, hlo, hhi, hg'⟩
    · exact good_implies_silent R e₀ ht hg
    · have hlt : e - e₀ < k := by omega
      have he : e₀ + (e - e₀) = e := Nat.add_sub_of_le hlo
      apply ih (e - e₀) hlt
      simpa [he] using hg'

theorem good_exists_implies_silent
    (h : ∃ e, e₀ ≤ e ∧ Good R e) : (system R e₀).EventuallySilent := by
  obtain ⟨e, hlo, hg⟩ := h
  have he : e₀ + (e - e₀) = e := Nat.add_sub_of_le hlo
  apply good_rank_implies_silent R e₀ (e - e₀)
  simpa [he] using hg

/-- Every candidate encountered is at or above the configured start. -/
theorem candidate_lower_bound (t : Nat) :
    ∀ e n, (system R e₀).run t = .testing e n → e₀ ≤ e := by
  induction t with
  | zero => simp [EventSystem.run, system]
  | succ t ih =>
    intro e n hs
    cases hst : (system R e₀).run t with
    | startup =>
      rw [EventSystem.run_succ, hst] at hs
      simp [system, step] at hs
      omega
    | testing a b =>
      have ha := ih a b hst
      cases hr : R a b with
      | false =>
        have hn := failure_step R e₀ hst hr
        rw [hn] at hs
        cases hs
        omega
      | true =>
        have hn := success_step R e₀ hst hr
        rw [hn] at hs
        cases hs
        exact ha

/-- A silent suffix continues through all tests of its current candidate. -/
theorem silent_testing_run {t e n : Nat}
    (hs : (system R e₀).run t = .testing e n)
    (hquiet : ∀ s, t ≤ s → ¬ (system R e₀).BeepAt s) :
    ∀ k, (system R e₀).run (t + k) = .testing e (n + k) ∧
      R e (n + k) = true := by
  intro k
  induction k with
  | zero =>
    have hne := hquiet t (Nat.le_refl t)
    have htrue : R e n = true := by
      cases hr : R e n with
      | false => exact False.elim (hne ((testing_beep_iff R e₀ hs).2 hr))
      | true => rfl
    exact ⟨by simpa using hs, by simpa using htrue⟩
  | succ k ih =>
    have hnext := success_step R e₀ ih.1 ih.2
    have hstate : (system R e₀).run (t + (k + 1)) = .testing e (n + (k + 1)) := by
      simpa [Nat.add_assoc] using hnext
    have hne := hquiet (t + (k + 1)) (by omega)
    have htrue : R e (n + (k + 1)) = true := by
      cases hr : R e (n + (k + 1)) with
      | false => exact False.elim (hne ((testing_beep_iff R e₀ hstate).2 hr))
      | true => rfl
    exact ⟨hstate, htrue⟩

theorem silent_implies_good_exists
    (h : (system R e₀).EventuallySilent) : ∃ e, e₀ ≤ e ∧ Good R e := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨e, n, hs⟩ := run_testing_succ R e₀ T
  have hquiet : ∀ s, T + 1 ≤ s → ¬ (system R e₀).BeepAt s := by
    intro s hts
    exact hT s (by omega)
  refine ⟨e, candidate_lower_bound R e₀ (T + 1) e n hs, ?_⟩
  intro i
  by_cases hlt : i < n
  · exact tested_prefix R e₀ (T + 1) e n hs i hlt
  · have hn : n ≤ i := by omega
    have ht := (silent_testing_run R e₀ hs hquiet (i - n)).2
    simpa [Nat.add_sub_of_le hn] using ht

/-- Initial beep at transition zero; then one beep for each rejected candidate.
The theorem is about the atomic comparison model, not its implementation. -/
theorem eventuallySilent_iff_exists_good :
    (system R e₀).EventuallySilent ↔ ∃ e, e₀ ≤ e ∧ Good R e :=
  ⟨silent_implies_good_exists R e₀, good_exists_implies_silent R e₀⟩

theorem all_bad_infinitely_many_beeps
    (hbad : ∀ e, e₀ ≤ e → ¬ Good R e) :
    ∀ T, ∃ t, T ≤ t ∧ (system R e₀).BeepAt t := by
  intro T
  apply Classical.byContradiction
  intro hn
  have hs : (system R e₀).EventuallySilent := by
    refine ⟨T, ?_⟩
    intro t ht hb
    exact hn ⟨t, ht, hb⟩
  obtain ⟨e, he, hg⟩ := (eventuallySilent_iff_exists_good R e₀).1 hs
  exact hbad e he hg

/-- Successful tests advance one index per transition until the first failure. -/
theorem testing_run_before_failure {t e n k : Nat}
    (hs : (system R e₀).run t = .testing e n)
    (hprior : ∀ i, i < k → R e (n + i) = true) :
    ∀ i, i ≤ k → (system R e₀).run (t + i) = .testing e (n + i) := by
  intro i
  induction i with
  | zero => intro _; simpa using hs
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hnext := success_step R e₀ hprev (hprior i (by omega))
    simpa [Nat.add_assoc] using hnext

/-- A least failing test gives exact transition timing, including the beep. -/
theorem first_failure_trace {t e n k : Nat}
    (hs : (system R e₀).run t = .testing e n)
    (hprior : ∀ i, i < k → R e (n + i) = true)
    (hf : R e (n + k) = false) :
    (∀ i, i < k → ¬ (system R e₀).BeepAt (t + i)) ∧
    (system R e₀).BeepAt (t + k) ∧
    (system R e₀).run (t + k + 1) = .testing (e + 1) 0 := by
  have htrace := testing_run_before_failure R e₀ hs hprior
  refine ⟨?_, (testing_beep_iff R e₀ (htrace k (Nat.le_refl k))).2 hf, ?_⟩
  · intro i hi
    rw [testing_beep_iff R e₀ (htrace i (by omega))]
    simp [hprior i hi]
  · exact failure_step R e₀ (htrace k (Nat.le_refl k)) hf

/-- The least good candidate above the starting index is actually reached. -/
theorem least_good_reached {e : Nat} (he : e₀ ≤ e) (_hg : Good R e)
    (hfirst : ∀ e', e₀ ≤ e' → e' < e → ¬ Good R e') :
    ∃ t, (system R e₀).run t = .testing e 0 := by
  have heq : e₀ + (e - e₀) = e := Nat.add_sub_of_le he
  rcases reach_or_earlier_good R e₀ (e - e₀) with ⟨t, ht⟩ | ⟨e', hlo, hhi, hg'⟩
  · exact ⟨t, by simpa [heq] using ht⟩
  · have hlt : e' < e := by simpa [heq] using hhi
    exact False.elim (hfirst e' hlo hlt hg')

/-- A failing candidate has a least failing test. This uses classical
reasoning only to prove existence; the transition function does not use it. -/
theorem first_failure_exists {e : Nat} (h : ∃ n, R e n = false) :
    ∃ k, R e k = false ∧ ∀ i, i < k → R e i = true := by
  classical
  have aux : ∀ n, R e n = false →
      ∃ k, R e k = false ∧ ∀ i, i < k → R e i = true := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases hp : ∀ i, i < n → R e i = true
      · exact ⟨n, hn, hp⟩
      · obtain ⟨i, hi⟩ := Classical.not_forall.mp hp
        have hlt : i < n := by
          by_cases hlt : i < n
          · exact hlt
          · exact False.elim (hi (fun h => False.elim (hlt h)))
        have hne : R e i ≠ true := fun hr => hi (fun _ => hr)
        have hf : R e i = false := by
          cases hr : R e i with
          | false => rfl
          | true => exact False.elim (hne hr)
        exact ih i hlt hf
  obtain ⟨n, hn⟩ := h
  exact aux n hn

/-- With no good candidates from the start onward, every candidate is reached. -/
theorem all_bad_reaches_every_candidate
    (hbad : ∀ e, e₀ ≤ e → ¬ Good R e) (k : Nat) :
    ∃ t, (system R e₀).run t = .testing (e₀ + k) 0 := by
  rcases reach_or_earlier_good R e₀ k with ⟨t, ht⟩ | ⟨e, he, _, hg⟩
  · exact ⟨t, ht⟩
  · exact False.elim (hbad e he hg)

/-- The zero-start instance has exactly the unqualified candidate quantifier. -/
theorem eventuallySilent_zero_iff_exists_good :
    (system R 0).EventuallySilent ↔ ∃ e, Good R e := by
  simpa using eventuallySilent_iff_exists_good R 0

end Shared.Beeping.Controller
