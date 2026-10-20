import CollatzTM.SixteenEntry
import CollatzTM.SixteenOdd
import CollatzTM.Global

namespace CollatzTM.M16

theorem init_exact : Reaches delta 4 blank (canonical 2 2) :=
  reaches_no_early delta 4 blank (canonical 2 2) init (by simp [canonical])

theorem strict_after_rch {a b c : Config State} (ha : StrictReach delta a b)
    (hb : Rch b c) : StrictReach delta a c := by
  obtain ⟨n, hn, he⟩ := ha
  obtain ⟨m, hm⟩ := hb
  exact ⟨n+m, by omega, by rw [run_add, he, hm]⟩

theorem odd_entry_strict (M k : Nat) (hk : 1 ≤ k) (hM : 2*k+1 ≤ M) :
    StrictReach delta (canonical M (2*k+1)) (cfg .J k (holes M k (k+1))) := by
  obtain ⟨n, hn, hr⟩ := Rch.exact_pos (odd_entry M k hk hM) (by simp [cfg]) (by
    intro h
    have hh := congrArg Config.state h
    simp [canonical, cfg] at hh)
  exact ⟨n, hn, hr.1⟩

theorem machine_spec : CycleMachineSpec delta blank canonical := by
  refine ⟨⟨4, init⟩, ?_, ?_, ?_⟩
  · intro M v _ _ _
    simp [canonical]
  · intro M hM
    obtain ⟨n, hn, hr⟩ := reset_pos M hM
    exact ⟨n, hn, hr.1⟩
  · intro M v hM hv hvM
    by_cases hp : v % 2 = 0
    · have he : v = 2*(v/2) := by omega
      have hk : 1 ≤ v/2 := by omega
      have hbound : 2*(v/2) ≤ M := by omega
      obtain ⟨n, hn, hr⟩ := even_macro_pos M (v/2) hk hbound
      rw [← he] at hr
      have hs := Arithmetic.shortcut_even v hp
      have hsmall : v/2 < M := by omega
      rw [hs]
      exact ⟨fun _ => ⟨n, hn, hr.1⟩, fun h => False.elim (by omega), fun h => False.elim (by omega)⟩
    · have hp1 : v % 2 = 1 := by omega
      have he : v = 2*(v/2)+1 := by omega
      have hk : 1 ≤ v/2 := by omega
      have hbound : 2*(v/2)+1 ≤ M := by omega
      have hs : Arithmetic.shortcut v = 3*(v/2)+2 := by
        rw [Arithmetic.shortcut_odd v hp1]
        omega
      have hr := odd_macro M (v/2) hk hbound
      rw [← he] at hr
      rw [hs]
      exact ⟨fun h => by obtain ⟨n, hn, hh⟩ := hr.1 h; exact ⟨n, hn, hh.1⟩,
        hr.2.1, fun h => by obtain ⟨n, hn, hh⟩ := hr.2.2 h; exact ⟨n, hn, hh.1⟩⟩

theorem halts_iff_shortcut_cycle :
    Halts delta blank ↔ Arithmetic.ShortcutCounter :=
  cycle_machine_correct delta blank canonical machine_spec

theorem halts_iff_ordinary_cycle :
    Halts delta blank ↔ Arithmetic.OrdinaryCounter :=
  cycle_machine_ordinary_correct delta blank canonical machine_spec

theorem exact_halt_of_live_rch {a b c : Config State} (h : Rch a b)
    (hb : b.state ≠ none) (hs : step delta b = c) :
    ∃ n, Reaches delta n a c := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n+1, ?_, ?_⟩
  · rw [run_add, hn]
    simpa [run] using hs
  · intro j hj
    by_cases hlt : j < n
    · exact (reaches_no_early delta n a b hn hb).2 j hlt
    · have he : j = n := by omega
      rw [he, hn]
      exact hb

/-- Equality branch: complete tape, final head, finite duration and no early halt. -/
theorem odd_macro_halt_exact (M k : Nat) (hk : 1 ≤ k) (hM : 2*k+1 ≤ M)
    (heq : 3*k+2 = M) :
    ∃ n, Reaches delta n (canonical M (2*k+1))
      ⟨none, (M : Int)+1, hole M ((M : Int)-1)⟩ := by
  have hr := rebuild k M (k+1) (by omega) (by omega)
  have hinside : (k+1 : Int)+2*(k : Int) < M := by omega
  rw [if_pos hinside] at hr
  have hre : (k+1 : Int)+2*(k : Int) = (M : Int)-1 := by omega
  rw [hre] at hr
  have ha := (odd_entry M k hk hM).trans hr
  have hb : Rch (cfg .N 0 (hole M ((M : Int)-1)))
      (cfg .N ((M : Int)-1) (hole M ((M : Int)-1))) := by
    apply right_to .N rfl _ _ _ (by omega)
    intro z hz hz'
    simp [hole]
    omega
  have ht : hole (M : Int) ((M : Int)-1) ((M : Int)-1) = false := by simp [hole]
  have e1 : step delta (cfg .N ((M : Int)-1) (hole M ((M : Int)-1))) =
      cfg .O M (hole M ((M : Int)-1)) := by
    simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
  have hO : Rch (canonical M (2*k+1)) (cfg .O M (hole M ((M : Int)-1))) :=
    ha.trans (hb.trans (Rch.of_step e1))
  apply exact_halt_of_live_rch hO (by simp [cfg])
  have ht' : hole (M : Int) ((M : Int)-1) M = false := by simp [hole]
  simp [step, cfg, ht', delta, move, put_same _ _ _ ht']

end CollatzTM.M16
