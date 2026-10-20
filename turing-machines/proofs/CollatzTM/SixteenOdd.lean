import CollatzTM.Sixteen
import CollatzTM.SixteenEntry

namespace CollatzTM.M16

theorem Rch.halts {a b : Config State} (h : Rch a b) (hb : Halts delta b) :
    Halts delta a := by
  obtain ⟨n, hn⟩ := h
  exact (halts_iff_of_run delta n a b hn).2 hb

theorem odd_cleanup (m g x : Int) (hg : 0 ≤ g) (hgm : g < m)
    (hgx : g ≤ x) (hxm : x < m) :
    Rch (cfg .A x (hole m g)) (cfg .D 0 (block m)) := by
  have hs : Rch (cfg .A x (hole m g)) (cfg .A g (hole m g)) := by
    apply left_to .A rfl _ _ _ hgx
    intro z hz hz'
    simp only [hole, decide_eq_true_eq]
    omega
  apply hs.trans
  have ht : hole m g g = false := by simp [hole]
  have he : step delta (cfg .A g (hole m g)) = cfg .P (g+1) (block m) := by
    simp [step, cfg, ht, delta, move, put_hole_true m g hg hgm]
  exact (Rch.of_step he).trans (grow m (g+1) (by omega) (by omega) (by omega))

theorem odd_finish_below (m r : Int) (hr : 0 ≤ r) (hrm : r < m-1) :
    Rch (cfg .N 0 (hole m r)) (cfg .D 0 (hole m r)) := by
  have hs : Rch (cfg .N 0 (hole m r)) (cfg .N r (hole m r)) := by
    apply right_to .N rfl _ _ _ hr
    intro z hz hz'
    simp only [hole, decide_eq_true_eq]
    omega
  apply hs.trans
  have ht : hole m r r = false := by simp [hole]
  have he : step delta (cfg .N r (hole m r)) = cfg .O (r+1) (hole m r) := by
    simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
  apply (Rch.of_step he).trans
  have ht1 : hole m r (r+1) = true := by simp only [hole, decide_eq_true_eq]; omega
  have he1 : step delta (cfg .O (r+1) (hole m r)) = cfg .B r (hole m r) := by
    simp [step, cfg, ht1, delta, move, put_same _ _ _ ht1]
    omega
  apply (Rch.of_step he1).trans
  have he2 : step delta (cfg .B r (hole m r)) = cfg .C (r-1) (hole m r) := by
    simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
    omega
  exact (Rch.of_step he2).trans (home m r (r-1) hr (by omega) (by omega) (by omega))

theorem odd_finish_equal (m r : Int) (hr : 0 ≤ r) (hrm : r = m-1) :
    Halts delta (cfg .N 0 (hole m r)) := by
  have hs : Rch (cfg .N 0 (hole m r)) (cfg .N r (hole m r)) := by
    apply right_to .N rfl _ _ _ hr
    intro z hz hz'
    simp only [hole, decide_eq_true_eq]
    omega
  apply hs.halts
  have ht : hole m r r = false := by simp [hole]
  have he : step delta (cfg .N r (hole m r)) = cfg .O (r+1) (hole m r) := by
    simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
  apply (Rch.of_step he).halts
  refine ⟨1, ?_⟩
  have ht1 : hole m r (r+1) = false := by simp only [hole, decide_eq_false_iff_not]; omega
  simp [run, step, cfg, ht1, delta]

def OddResult (m r : Int) (a : Config State) : Prop :=
  (r < m-1 → Rch a (cfg .D 0 (hole m r))) ∧
  (r = m-1 → Halts delta a) ∧
  (m-1 < r → Rch a (cfg .D 0 (block m)))

theorem OddResult.back {m r : Int} {a b : Config State}
    (h : Rch a b) (hb : OddResult m r b) : OddResult m r a := by
  exact ⟨fun he => h.trans (hb.1 he), fun he => h.halts (hb.2.1 he),
    fun he => h.trans (hb.2.2 he)⟩

theorem odd_loop : ∀ (g : Nat) (m h : Int), (g : Int) < h → h < m →
    OddResult m (h+2*g) (cfg .J g (holes m g h)) := by
  intro g
  induction g with
  | zero =>
    intro m h hgh hhm
    have ht : holes m 0 h 0 = false := by simp [holes]
    have he : step delta (cfg .J 0 (holes m 0 h)) = cfg .K (-1) (hole m h) := by
      simp [step, cfg, ht, delta, move,
        put_holes_left_true m 0 h (by omega) (by omega) (by omega)]
    apply OddResult.back (Rch.of_step he)
    have ht1 : hole m h (-1) = false := by simp [hole]
    have he1 : step delta (cfg .K (-1) (hole m h)) = cfg .N 0 (hole m h) := by
      simp [step, cfg, ht1, delta, move, put_same _ _ _ ht1]
    apply OddResult.back (Rch.of_step he1)
    simp only [Int.natCast_zero, Int.mul_zero, Int.add_zero]
    exact ⟨odd_finish_below m h (by omega), odd_finish_equal m h (by omega), by omega⟩
  | succ g ih =>
    intro m h hgh hhm
    have hg0 : (0 : Int) ≤ g := by omega
    have ht : holes m (g+1) h (g+1) = false := by simp [holes]
    have he : step delta (cfg .J (g+1) (holes m (g+1) h)) = cfg .K g (hole m h) := by
      simp [step, cfg, ht, delta, move,
        put_holes_left_true m (g+1) h (by omega) (by omega) (by omega)]
      omega
    have ht1 : hole m h g = true := by simp only [hole, decide_eq_true_eq]; omega
    have he1 : step delta (cfg .K g (hole m h)) = cfg .L (g+1) (holes m g h) := by
      simp [step, cfg, ht1, delta, move, put_hole_false]
    have hs : Rch (cfg .L (g+1) (holes m g h)) (cfg .L h (holes m g h)) := by
      apply right_to .L rfl _ _ _ (by omega)
      intro z hz hz'
      simp only [holes, decide_eq_true_eq]
      omega
    have ht2 : holes m g h h = false := by simp [holes]
    have he2 : step delta (cfg .L h (holes m g h)) = cfg .M (h+1) (hole m g) := by
      simp [step, cfg, ht2, delta, move,
        put_holes_right_true m g h (by omega) (by omega) (by omega)]
    have pre : Rch (cfg .J (g+1) (holes m (g+1) h)) (cfg .M (h+1) (hole m g)) :=
      (Rch.of_step he).trans ((Rch.of_step he1).trans (hs.trans (Rch.of_step he2)))
    apply OddResult.back pre
    by_cases hfirst : h+1 = m
    · have ht3 : hole m g (h+1) = false := by simp only [hole, decide_eq_false_iff_not]; omega
      have he3 : step delta (cfg .M (h+1) (hole m g)) = cfg .A h (hole m g) := by
        simp [step, cfg, ht3, delta, move, put_same _ _ _ ht3]
        omega
      have hr := (Rch.of_step he3).trans (odd_cleanup m g h (by omega) (by omega) (by omega) (by omega))
      exact ⟨by omega, by omega, fun _ => hr⟩
    · have h1m : h+1 < m := by omega
      have ht3 : hole m g (h+1) = true := by simp only [hole, decide_eq_true_eq]; omega
      have he3 : step delta (cfg .M (h+1) (hole m g)) = cfg .I (h+2) (hole m g) := by
        simp [step, cfg, ht3, delta, move, put_same _ _ _ ht3]
        omega
      apply OddResult.back (Rch.of_step he3)
      by_cases hsecond : h+2=m
      · have ht4 : hole m g (h+2) = false := by simp only [hole, decide_eq_false_iff_not]; omega
        have he4 : step delta (cfg .I (h+2) (hole m g)) = cfg .A (h+1) (hole m g) := by
          simp [step, cfg, ht4, delta, move, put_same _ _ _ ht4]
          omega
        have hr := (Rch.of_step he4).trans (odd_cleanup m g (h+1) (by omega) (by omega) (by omega) (by omega))
        exact ⟨by omega, by omega, fun _ => hr⟩
      · have h2m : h+2<m := by omega
        have ht4 : hole m g (h+2) = true := by simp only [hole, decide_eq_true_eq]; omega
        have he4 : step delta (cfg .I (h+2) (hole m g)) = cfg .J (h+1) (holes m g (h+2)) := by
          simp [step, cfg, ht4, delta, move, put_hole_false, holes_comm m (h+2) g]
          omega
        have hs' : Rch (cfg .J (h+1) (holes m g (h+2))) (cfg .J g (holes m g (h+2))) := by
          apply left_to .J rfl _ _ _ (by omega)
          intro z hz hz'
          simp only [holes, decide_eq_true_eq]
          omega
        have hh := OddResult.back ((Rch.of_step he4).trans hs') (ih m (h+2) (by omega) h2m)
        have heq : h+2+2*(g:Int)=h+2*(↑(g+1):Int) := by omega
        rw [heq] at hh
        exact hh

theorem odd_rebuild (M k : Nat) (hk : 1 ≤ k) (hM : 2*k+1 ≤ M) :
    let a := cfg .J k (holes M k (k+1))
    (3*k+2 < M → ∃ n, Reaches delta n a (canonical M (3*k+2))) ∧
    (3*k+2 = M → Halts delta a) ∧
    (M < 3*k+2 → ∃ n, Reaches delta n a (canonical (M+1) (M+1))) := by
  dsimp only
  have h := odd_loop k M (k+1) (by omega) (by omega)
  have ht : (k+1 : Int)+2*(k:Int) = ((3*k+2 : Nat) : Int)-1 := by omega
  rw [ht] at h
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    have hr := h.1 (by omega)
    exact Rch.exact hr (by simp [canonical])
  · intro heq
    exact h.2.1 (by omega)
  · intro hgt
    have hr := h.2.2 (by omega)
    have hn : cfg .D 0 (block M) = canonical (M+1) (M+1) := by
      simp [canonical, cfg, block_eq_next_hole, Int.natCast_add]
    rw [hn] at hr
    exact Rch.exact hr (by simp [canonical])

theorem odd_macro (M k : Nat) (hk : 1 ≤ k) (hM : 2*k+1 ≤ M) :
    (3*k+2 < M → ∃ n, 0 < n ∧ Reaches delta n
      (canonical M (2*k+1)) (canonical M (3*k+2))) ∧
    (3*k+2 = M → Halts delta (canonical M (2*k+1))) ∧
    (M < 3*k+2 → ∃ n, 0 < n ∧ Reaches delta n
      (canonical M (2*k+1)) (canonical (M+1) (M+1))) := by
  have he := odd_entry M k hk hM
  have hr := odd_rebuild M k hk hM
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    obtain ⟨n, hn⟩ := hr.1 hlt
    apply Rch.exact_pos (he.trans ⟨n, hn.1⟩) (by simp [canonical])
    intro heq
    have hne := canonical_inj M (2*k+1) (3*k+2) (by omega) hM
      (by omega) (by omega) heq
    omega
  · intro heq
    exact he.halts (hr.2.1 heq)
  · intro hgt
    obtain ⟨n, hn⟩ := hr.2.2 hgt
    apply Rch.exact_pos (he.trans ⟨n, hn.1⟩) (by simp [canonical])
    intro heq
    have ht := congrArg (fun c : Config State => c.tape ((2*k+1 : Nat)-1)) heq
    simp only [canonical, hole] at ht
    simp at ht
    omega

end CollatzTM.M16
