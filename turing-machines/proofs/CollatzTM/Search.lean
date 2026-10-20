import CollatzTM.Core
import CollatzTM.Arithmetic

namespace CollatzTM

def StrictReach (δ : S → Bool → Instr S) (a b : Config S) : Prop :=
  ∃ t, 0 < t ∧ run δ t a = b

theorem StrictReach.trans {δ : S → Bool → Instr S} {a b c : Config S}
    (h : StrictReach δ a b) (h' : StrictReach δ b c) : StrictReach δ a c := by
  obtain ⟨t, ht, he⟩ := h
  obtain ⟨u, hu, hf⟩ := h'
  exact ⟨t+u, by omega, by rw [run_add, he, hf]⟩

theorem StrictReach.halts_iff {δ : S → Bool → Instr S} {a b : Config S}
    (h : StrictReach δ a b) : Halts δ a ↔ Halts δ b := by
  obtain ⟨t, _, he⟩ := h
  exact halts_iff_of_run δ t a b he

theorem not_halts_of_progress (δ : S → Bool → Instr S) (P : Config S → Prop)
    (live : ∀ c, P c → c.state ≠ none)
    (progress : ∀ c, P c → ∃ c', P c' ∧ StrictReach δ c c') :
    ∀ c, P c → ¬ Halts δ c := by
  suffices H : ∀ N c, P c → (run δ N c).state ≠ none by
    intro c hc ⟨N, hN⟩
    exact H N c hc hN
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro c hc hN
    obtain ⟨c', hc', t, ht, hrun⟩ := progress c hc
    by_cases htN : t ≤ N
    · have he := run_add δ t (N-t) c
      rw [Nat.add_sub_of_le htN, hrun] at he
      exact ih (N-t) (by omega) c' hc' (by rw [← he]; exact hN)
    · exact (reaches_no_early δ t c c' hrun (live c' hc')).2 N (by omega) hN

open Arithmetic

/-- Explicit interface required from a concrete cycle detector's tape macros.
The global theorem below does not assert that either supplied table satisfies it. -/
structure CycleMachineSpec (δ : S → Bool → Instr S) (start : Config S)
    (C : Nat → Nat → Config S) : Prop where
  init : ∃ t, run δ t start = C 2 2
  live : ∀ M v, 2 ≤ M → 1 ≤ v → v ≤ M → (C M v).state ≠ none
  reset : ∀ M, 2 ≤ M → StrictReach δ (C M 1) (C (M+1) (M+1))
  advance : ∀ M v, 2 ≤ M → 2 ≤ v → v ≤ M →
    (shortcut v < M → StrictReach δ (C M v) (C M (shortcut v))) ∧
    (shortcut v = M → Halts δ (C M v)) ∧
    (M < shortcut v → StrictReach δ (C M v) (C (M+1) (M+1)))

def RoundOutcome (δ : S → Bool → Instr S) (C : Nat → Nat → Config S)
    (M final : Nat) (a : Config S) : Prop :=
  (final = M → Halts δ a) ∧
  (final ≠ M → StrictReach δ a (C (M+1) (M+1)))

theorem RoundOutcome.back {δ : S → Bool → Instr S} {C : Nat → Nat → Config S}
    {M final : Nat} {a b : Config S} (hr : StrictReach δ a b)
    (h : RoundOutcome δ C M final b) : RoundOutcome δ C M final a := by
  exact ⟨fun he => hr.halts_iff.2 (h.1 he), fun he => hr.trans (h.2 he)⟩

theorem cycle_round_run (δ : S → Bool → Instr S) (start : Config S)
    (C : Nat → Nat → Config S) (spec : CycleMachineSpec δ start C)
    (M : Nat) (hM : 2 ≤ M) :
    ∀ i x, 2 ≤ x → x ≤ M →
    (∀ j, j < i → ¬ Cond M (it (j+1) x)) → Cond M (it (i+1) x) →
    RoundOutcome δ C M (it (i+1) x) (C M x) := by
  intro i
  induction i with
  | zero =>
    intro x hx hxM _ hc
    have hs := spec.advance M x hM hx hxM
    have hpos := shortcut_pos x (by omega)
    constructor
    · exact hs.2.1
    · intro hne
      rcases hc with h1 | hge
      · have hsmall : shortcut x < M := by change shortcut x = 1 at h1; omega
        have h1' : shortcut x = 1 := h1
        have hr := hs.1 hsmall
        rw [h1'] at hr
        exact hr.trans (spec.reset M hM)
      · exact hs.2.2 (by change M ≤ shortcut x at hge; change shortcut x ≠ M at hne; omega)
  | succ i ih =>
    intro x hx hxM hfirst hc
    have h0 := hfirst 0 (by omega)
    have hpos := shortcut_pos x (by omega)
    have hsmall : shortcut x < M := by change ¬ (shortcut x = 1 ∨ M ≤ shortcut x) at h0; omega
    have hx' : 2 ≤ shortcut x := by change ¬ (shortcut x = 1 ∨ M ≤ shortcut x) at h0; omega
    have hr := (spec.advance M x hM hx hxM).1 hsmall
    have ht : RoundOutcome δ C M (it (i+1) (shortcut x)) (C M (shortcut x)) := by
      apply ih (shortcut x) hx' (by omega)
      · intro j hj
        have h := hfirst (j+1) (by omega)
        simpa only [it_succ'] using h
      · simpa only [it_succ'] using hc
    have h := RoundOutcome.back hr ht
    simpa only [it_succ'] using h

theorem cycle_machine_correct (δ : S → Bool → Instr S) (start : Config S)
    (C : Nat → Nat → Config S) (spec : CycleMachineSpec δ start C) :
    Halts δ start ↔ Counter := by
  obtain ⟨seed, hseed⟩ := spec.init
  have round := fun M hM i hf hc => cycle_round_run δ start C spec M hM i M hM
    (Nat.le_refl M) hf hc
  constructor
  · intro hhalt
    apply Classical.byContradiction
    intro hno
    have live : ∀ c, (∃ M, 2 ≤ M ∧ c = C M M) → c.state ≠ none := by
      rintro c ⟨M, hM, rfl⟩
      exact spec.live M M hM (by omega) (Nat.le_refl M)
    have progress : ∀ c, (∃ M, 2 ≤ M ∧ c = C M M) →
        ∃ c', (∃ M, 2 ≤ M ∧ c' = C M M) ∧ StrictReach δ c c' := by
      rintro c ⟨M, hM, rfl⟩
      obtain ⟨i, hi, hf⟩ := first_index (round_stops M (by omega) (nocyc_of_not hno M))
      have hne := round_no_return M (by omega) (nocyc_of_not hno (M+1)) i hf
      exact ⟨C (M+1) (M+1), ⟨M+1, by omega, rfl⟩, (round M hM i hf hi).2 hne⟩
    exact not_halts_of_progress δ _ live progress (C 2 2) ⟨2, by omega, rfl⟩
      ((halts_iff_of_run δ seed start _ hseed).1 hhalt)
  · intro hcounter
    obtain ⟨M, hM, hsmall, k, hk, he, hbnd⟩ := exists_top hcounter
    have hlast : Halts δ (C M M) := by
      obtain ⟨i, hi, hf⟩ := first_index (P := fun i => Cond M (it (i+1) M))
        ⟨k-1, Or.inr (by rw [show k-1+1=k by omega, he]; exact Nat.le_refl M)⟩
      have hiK : i+1 ≤ k := by
        apply Classical.byContradiction
        intro h
        exact hf (k-1) (by omega) (Or.inr (by rw [show k-1+1=k by omega, he]; exact Nat.le_refl M))
      have heq : it (i+1) M = M := by
        have := hbnd (i+1) hiK
        unfold Cond at hi
        omega
      exact (round M hM i hf hi).1 heq
    have earlier : ∀ d m, m+d=M → 2 ≤ m → Halts δ (C m m) := by
      intro d
      induction d with
      | zero =>
        intro m he _
        have hm : m=M := by omega
        rw [hm]
        exact hlast
      | succ d ih =>
        intro m he hm
        obtain ⟨i, hi, hf⟩ := first_index (round_stops m (by omega) (hsmall.mono (by omega)))
        by_cases heq : it (i+1) m = m
        · exact (round m hm i hf hi).1 heq
        · exact ((round m hm i hf hi).2 heq).halts_iff.2 (ih (m+1) (by omega) (by omega))
    exact (halts_iff_of_run δ seed start _ hseed).2 (earlier (M-2) 2 (by omega) (by omega))

end CollatzTM
