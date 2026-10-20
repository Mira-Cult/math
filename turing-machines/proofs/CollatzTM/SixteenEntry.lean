import CollatzTM.SixteenRebuild

namespace CollatzTM.M16

theorem odd_entry (M k : Nat) (hk : 1 ≤ k) (hM : 2*k+1 ≤ M) :
    Rch (canonical M (2*k+1)) (cfg .J k (holes M k (k+1))) := by
  have ht : hole (M : Int) (2*k) 0 = true := by simp [hole]; omega
  have e0 : step delta (canonical M (2*k+1)) = cfg .E 1 (hole M (2*k)) := by
    simp only [canonical, Int.natCast_add, Int.natCast_mul, Int.natCast_one]
    simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
  have ha := inward_odd (k-1) M 0 (by omega) (by omega)
  have h1 : (0 : Int)+2*(k-1 : Nat)+2 = 2*k := by omega
  have h2 : (0 : Int)+(k-1 : Nat)+1 = k := by omega
  have h3 : (0 : Int)+(k-1 : Nat)+2 = k+1 := by omega
  rw [h1, h2, h3] at ha
  simp only [Int.zero_add] at ha
  exact (Rch.of_step e0).trans ha

theorem Rch.exact_pos {a b : Config State} (h : Rch a b) (hb : b.state ≠ none)
    (hne : a ≠ b) : ∃ n, 0 < n ∧ Reaches delta n a b := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_, reaches_no_early delta n a b hn hb⟩
  by_cases he : n = 0
  · subst n
    exact False.elim (hne hn)
  · omega

theorem canonical_inj (M v w : Nat) (hv : 1 ≤ v) (hvM : v ≤ M)
    (hw : 1 ≤ w) (hwM : w ≤ M) (he : canonical M v = canonical M w) : v = w := by
  have ht := congrArg (fun c : Config State => c.tape ((v : Int)-1)) he
  simp only [canonical, hole] at ht
  have h0 : 0 ≤ (v : Int)-1 := by omega
  have h1 : (v : Int)-1 < M := by omega
  simp only [h0, h1, true_and, ne_eq, not_true_eq_false, decide_false] at ht
  have hh : ¬ ((v : Int)-1 ≠ (w : Int)-1) := by
    intro h
    simp [h] at ht
  omega

theorem even_macro_pos (M k : Nat) (hk : 1 ≤ k) (hM : 2*k ≤ M) :
    ∃ n, 0 < n ∧ Reaches delta n (canonical M (2*k)) (canonical M k) := by
  obtain ⟨n, hn⟩ := even_macro M k hk hM
  apply Rch.exact_pos ⟨n, hn.1⟩ (by simp [canonical])
  intro he
  have hh := canonical_inj M (2*k) k (by omega) hM hk (by omega) he
  omega

theorem reset_pos (M : Nat) (hm : 2 ≤ M) :
    ∃ n, 0 < n ∧ Reaches delta n (canonical M 1) (canonical (M+1) (M+1)) := by
  obtain ⟨n, hn⟩ := reset M hm
  apply Rch.exact_pos ⟨n, hn.1⟩ (by simp [canonical])
  intro he
  have ht := congrArg (fun c : Config State => c.tape 0) he
  simp [canonical, hole] at ht
  omega

end CollatzTM.M16
