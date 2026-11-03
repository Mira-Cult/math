import CollatzTM.SixteenEven

namespace CollatzTM.M16

theorem inward_odd (d : Nat) (m g : Int) (hg : 0 ≤ g) (hm : g+2*d+2 < m) :
    Rch (cfg .E (g+1) (hole m (g+2*d+2)))
      (cfg .J (g+d+1) (holes m (g+d+1) (g+d+2))) := by
  induction d generalizing g with
  | zero =>
    have ht : hole m (g+2) (g+1) = true := by simp [hole]; omega
    have e1 : step delta (cfg .E (g+1) (hole m (g+2))) = cfg .F (g+2) (holes m (g+1) (g+2)) := by
      simp [step, cfg, ht, delta, move, put_hole_false]
      omega
    have ht2 : holes m (g+1) (g+2) (g+2) = false := by simp [holes]
    have e2 : step delta (cfg .F (g+2) (holes m (g+1) (g+2))) = cfg .G (g+1) (hole m (g+1)) := by
      simp [step, cfg, ht2, delta, move, put_holes_right_true m (g+1) (g+2) (by omega) (by omega) (by omega)]
      omega
    have ht3 : hole m (g+1) (g+1) = false := by simp [hole]
    have e3 : step delta (cfg .G (g+1) (hole m (g+1))) = cfg .I (g+2) (hole m (g+1)) := by
      simp [step, cfg, ht3, delta, move, put_same _ _ _ ht3]
      omega
    have ht4 : hole m (g+1) (g+2) = true := by simp [hole]; omega
    have e4 : step delta (cfg .I (g+2) (hole m (g+1))) = cfg .J (g+1) (holes m (g+1) (g+2)) := by
      simp [step, cfg, ht4, delta, move, put_hole_false]
      constructor
      · omega
      · exact holes_comm _ _ _
    simpa using (Rch.of_step e1).trans ((Rch.of_step e2).trans ((Rch.of_step e3).trans (Rch.of_step e4)))
  | succ d ih =>
    have ha := inward_advance m g (g+2*(d+1)+2) hg (by omega) (by omega)
    have hb := ih (g+1) (by omega) (by omega)
    have eq1 : g+2*(d+1)+2-1 = (g+1)+2*d+2 := by omega
    have eq2 : g+2 = (g+1)+1 := by omega
    rw [eq1, eq2] at ha
    have eq3 : g+(d+1)+1 = (g+1)+d+1 := by omega
    have eq4 : g+(d+1)+2 = (g+1)+d+2 := by omega
    simp only [Int.natCast_add, Int.natCast_one]
    rw [eq3, eq4]
    exact ha.trans hb

theorem cleanup (m h x : Int) (hh : 0 ≤ h) (hm : h < m)
    (hx : h ≤ x) (hxm : x < m) :
    Rch (cfg .A x (hole m h)) (cfg .D 0 (block m)) := by
  have ha : Rch (cfg .A x (hole m h)) (cfg .A h (hole m h)) := by
    apply left_to .A rfl _ _ _ hx
    intro z hz hz'
    simp [hole]
    omega
  have ht : hole m h h = false := by simp [hole]
  have he : step delta (cfg .A h (hole m h)) = cfg .P (h+1) (block m) := by
    simp [step, cfg, ht, delta, move, put_hole_true m h hh hm]
  exact ha.trans ((Rch.of_step he).trans (grow m (h+1) (by omega) (by omega) (by omega)))

theorem rebuild_prefix (m g h : Int) (hg : 0 < g) (hgh : g < h) (hm : h < m) :
    Rch (cfg .J g (holes m g h)) (cfg .M (h+1) (hole m (g-1))) := by
  have ht : holes m g h g = false := by simp [holes]
  have e1 : step delta (cfg .J g (holes m g h)) = cfg .K (g-1) (hole m h) := by
    simp [step, cfg, ht, delta, move, put_holes_left_true m g h (by omega) (by omega) (by omega)]
    omega
  have ht2 : hole m h (g-1) = true := by simp [hole]; omega
  have e2 : step delta (cfg .K (g-1) (hole m h)) = cfg .L g (holes m (g-1) h) := by
    simp [step, cfg, ht2, delta, move, put_hole_false]
  have ha : Rch (cfg .L g (holes m (g-1) h)) (cfg .L h (holes m (g-1) h)) := by
    apply right_to .L rfl _ _ _ (by omega)
    intro z hz hz'
    simp [holes]
    omega
  have ht3 : holes m (g-1) h h = false := by simp [holes]
  have e3 : step delta (cfg .L h (holes m (g-1) h)) = cfg .M (h+1) (hole m (g-1)) := by
    simp [step, cfg, ht3, delta, move, put_holes_right_true m (g-1) h (by omega) hm (by omega)]
  exact (Rch.of_step e1).trans ((Rch.of_step e2).trans (ha.trans (Rch.of_step e3)))

theorem rebuild_advance (m g h : Int) (hg : 0 < g) (hgh : g < h) (hm : h+2 < m) :
    Rch (cfg .J g (holes m g h)) (cfg .J (g-1) (holes m (g-1) (h+2))) := by
  have ha := rebuild_prefix m g h hg hgh (by omega)
  have ht : hole m (g-1) (h+1) = true := by simp [hole]; omega
  have e1 : step delta (cfg .M (h+1) (hole m (g-1))) = cfg .I (h+2) (hole m (g-1)) := by
    simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
    omega
  have ht2 : hole m (g-1) (h+2) = true := by simp [hole]; omega
  have e2 : step delta (cfg .I (h+2) (hole m (g-1))) = cfg .J (h+1) (holes m (g-1) (h+2)) := by
    simp [step, cfg, ht2, delta, move, put_hole_false]
    constructor
    · omega
    · exact holes_comm _ _ _
  have hb : Rch (cfg .J (h+1) (holes m (g-1) (h+2))) (cfg .J (g-1) (holes m (g-1) (h+2))) := by
    apply left_to .J rfl _ _ _ (by omega)
    intro z hz hz'
    simp [holes]
    omega
  exact ha.trans ((Rch.of_step e1).trans ((Rch.of_step e2).trans hb))

theorem rebuild_overflow (m g h : Int) (hg : 0 < g) (hgh : g < h)
    (hm : h < m) (hov : m ≤ h+2) :
    Rch (cfg .J g (holes m g h)) (cfg .D 0 (block m)) := by
  have ha := rebuild_prefix m g h hg hgh hm
  apply ha.trans
  by_cases hb : h+1 < m
  · have ht : hole m (g-1) (h+1) = true := by simp [hole]; omega
    have e1 : step delta (cfg .M (h+1) (hole m (g-1))) = cfg .I (h+2) (hole m (g-1)) := by
      simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
      omega
    have ht2 : hole m (g-1) (h+2) = false := by simp [hole]; omega
    have e2 : step delta (cfg .I (h+2) (hole m (g-1))) = cfg .A (h+1) (hole m (g-1)) := by
      simp [step, cfg, ht2, delta, move, put_same _ _ _ ht2]
      omega
    exact (Rch.of_step e1).trans ((Rch.of_step e2).trans
      (cleanup m (g-1) (h+1) (by omega) (by omega) (by omega) hb))
  · have ht : hole m (g-1) (h+1) = false := by simp [hole]; omega
    have e1 : step delta (cfg .M (h+1) (hole m (g-1))) = cfg .A h (hole m (g-1)) := by
      simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
      omega
    exact (Rch.of_step e1).trans (cleanup m (g-1) h (by omega) (by omega) (by omega) hm)

theorem rebuild (g : Nat) (m h : Int) (hgh : (g : Int) < h) (hm : h < m) :
    if h+2*g < m then
      Rch (cfg .J g (holes m g h)) (cfg .N 0 (hole m (h+2*g)))
    else
      Rch (cfg .J g (holes m g h)) (cfg .D 0 (block m)) := by
  induction g generalizing h with
  | zero =>
    simp only [Int.natCast_zero, Int.mul_zero, Int.add_zero, hm, ↓reduceIte]
    have ht : holes m 0 h 0 = false := by simp [holes]
    have e1 : step delta (cfg .J 0 (holes m 0 h)) = cfg .K (-1) (hole m h) := by
      simp [step, cfg, ht, delta, move, put_holes_left_true m 0 h (by omega) (by omega) (by omega)]
    have ht2 : hole m h (-1) = false := by simp [hole]
    have e2 : step delta (cfg .K (-1) (hole m h)) = cfg .N 0 (hole m h) := by
      simp [step, cfg, ht2, delta, move, put_same _ _ _ ht2]
    exact (Rch.of_step e1).trans (Rch.of_step e2)
  | succ g ih =>
    by_cases hstep : h+2 < m
    · have ha := rebuild_advance m (g+1) h (by omega) (by omega) hstep
      have hb := ih (h+2) (by omega) hstep
      have e0 : (g : Int)+1-1 = g := by omega
      have e1 : (h+2)+2*g = h+2*(g+1 : Nat) := by omega
      rw [e0] at ha
      rw [e1] at hb
      split
      · rename_i hc
        rw [if_pos hc] at hb
        exact ha.trans hb
      · rename_i hc
        rw [if_neg hc] at hb
        exact ha.trans hb
    · have ht : ¬ (h+2*(g+1 : Nat) < m) := by omega
      rw [if_neg ht]
      exact rebuild_overflow m (g+1) h (by omega) (by omega) hm (by omega)

end CollatzTM.M16
