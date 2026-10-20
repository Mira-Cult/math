import CollatzTM.Sixteen

namespace CollatzTM.M16

theorem inward_advance (m g h : Int) (hg : 0 ≤ g) (hgap : g+3 ≤ h) (hm : h < m) :
    Rch (cfg .E (g+1) (hole m h)) (cfg .E (g+2) (hole m (h-1))) := by
  have ht : hole m h (g+1) = true := by simp [hole]; omega
  have e1 : step delta (cfg .E (g+1) (hole m h)) = cfg .F (g+2) (holes m (g+1) h) := by
    simp [step, cfg, ht, delta, move, put_hole_false]
    omega
  have s1 : Rch (cfg .F (g+2) (holes m (g+1) h)) (cfg .F h (holes m (g+1) h)) := by
    apply right_to .F rfl _ _ _ (by omega)
    intro z hz hz'
    simp [holes]
    omega
  have ht2 : holes m (g+1) h h = false := by simp [holes]
  have e2 : step delta (cfg .F h (holes m (g+1) h)) = cfg .G (h-1) (hole m (g+1)) := by
    simp [step, cfg, ht2, delta, move, put_holes_right_true m (g+1) h (by omega) hm (by omega)]
    omega
  have ht3 : hole m (g+1) (h-1) = true := by simp [hole]; omega
  have e3 : step delta (cfg .G (h-1) (hole m (g+1))) = cfg .H (h-2) (holes m (g+1) (h-1)) := by
    simp [step, cfg, ht3, delta, move, put_hole_false]
    constructor
    · omega
    · exact holes_comm _ _ _
  have s2 : Rch (cfg .H (h-2) (holes m (g+1) (h-1))) (cfg .H (g+1) (holes m (g+1) (h-1))) := by
    apply left_to .H rfl _ _ _ (by omega)
    intro z hz hz'
    simp [holes]
    omega
  have ht4 : holes m (g+1) (h-1) (g+1) = false := by simp [holes]
  have e4 : step delta (cfg .H (g+1) (holes m (g+1) (h-1))) = cfg .E (g+2) (hole m (h-1)) := by
    simp [step, cfg, ht4, delta, move, put_holes_left_true m (g+1) (h-1) (by omega) (by omega) (by omega)]
    omega
  exact (Rch.of_step e1).trans (s1.trans ((Rch.of_step e2).trans
    ((Rch.of_step e3).trans (s2.trans (Rch.of_step e4)))))

theorem inward_even (d : Nat) (m g : Int) (hg : 0 ≤ g) (hm : g+2*d+1 < m) :
    Rch (cfg .E (g+1) (hole m (g+2*d+1))) (cfg .B (g+d) (block m)) := by
  induction d generalizing g with
  | zero =>
    have ht : hole m (g+1) (g+1) = false := by simp [hole]
    apply Rch.of_step
    simp [step, cfg, delta, move, ht, put_hole_true m (g+1) (by omega) (by omega)]
    omega
  | succ d ih =>
    have ha := inward_advance m g (g+2*(d+1)+1) hg (by omega) (by omega)
    have hb := ih (g+1) (by omega) (by omega)
    have eq1 : g+2*(d+1)+1-1 = (g+1)+2*d+1 := by omega
    have eq2 : g+2 = (g+1)+1 := by omega
    have eq3 : g+(d+1) = (g+1)+d := by omega
    rw [eq1, eq2] at ha
    simp only [Int.natCast_add, Int.natCast_one]
    rw [eq3]
    exact ha.trans hb

theorem even_macro (M k : Nat) (hk : 1 ≤ k) (hM : 2*k ≤ M) :
    ∃ n, Reaches delta n (canonical M (2*k)) (canonical M k) := by
  apply Rch.exact _ (by simp [canonical])
  have h0 : hole (M : Int) (2*(k : Int)-1) 0 = true := by simp [hole]; omega
  have e0 : step delta (canonical M (2*k)) = cfg .E 1 (hole M (2*k-1)) := by
    simp only [canonical, Int.natCast_mul]
    simp [step, cfg, h0, delta, move, put_same _ _ _ h0]
  have ha := inward_even (k-1) M 0 (by omega) (by omega)
  have h1 : (0 : Int)+2*(k-1 : Nat)+1 = 2*k-1 := by omega
  have h2 : (0 : Int)+(k-1 : Nat) = (k : Int)-1 := by omega
  rw [h1, h2] at ha
  simp only [Int.zero_add] at ha
  have e1 : step delta (cfg .B (k-1) (block M)) = cfg .C (k-2) (hole M (k-1)) := by
    by_cases ht : block (M : Int) (k-1) = true
    · simp [step, cfg, ht, delta, move, put_block_false]
      omega
    · have ht' : block (M : Int) (k-1) = false := Bool.eq_false_iff.mpr ht
      simp [step, cfg, ht', delta, move, put_block_false]
      omega
  have hb := home M (k-1) (k-2) (by omega) (by omega) (by omega) (by omega)
  have hc : cfg .D 0 (hole M (k-1)) = canonical M k := rfl
  rw [hc] at hb
  exact (Rch.of_step e0).trans (ha.trans ((Rch.of_step e1).trans hb))

end CollatzTM.M16
