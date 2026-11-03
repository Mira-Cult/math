import CollatzTM.Machine16

namespace CollatzTM.M16

def block (m : Int) : Tape := fun z => decide (0 ≤ z ∧ z < m)
def hole (m h : Int) : Tape := fun z => decide (0 ≤ z ∧ z < m ∧ z ≠ h)
def holes (m g h : Int) : Tape := fun z => decide (0 ≤ z ∧ z < m ∧ z ≠ g ∧ z ≠ h)

def canonical (M v : Nat) : Config State :=
  ⟨some .D, 0, hole M ((v : Int)-1)⟩

def cfg (q : State) (p : Int) (t : Tape) : Config State := ⟨some q, p, t⟩
def Rch (a b : Config State) : Prop := ∃ n, run delta n a = b

theorem Rch.refl (a : Config State) : Rch a a := ⟨0, rfl⟩
theorem Rch.trans {a b c : Config State} (h : Rch a b) (h' : Rch b c) : Rch a c := by
  rcases h with ⟨n, hn⟩
  rcases h' with ⟨m, hm⟩
  exact ⟨n+m, by rw [run_add, hn, hm]⟩

theorem Rch.exact {a b : Config State} (h : Rch a b) (hb : b.state ≠ none) :
    ∃ n, Reaches delta n a b := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, reaches_no_early delta n a b hn hb⟩

theorem put_same (t : Tape) (p : Int) (b : Bool) (h : t p = b) : put t p b = t := by
  funext z
  simp only [put]
  split <;> simp_all

theorem put_block_false (m h : Int) : put (block m) h false = hole m h := by
  funext z
  simp only [put, block, hole]
  split <;> simp_all

theorem put_hole_true (m h : Int) (h0 : 0 ≤ h) (hm : h < m) :
    put (hole m h) h true = block m := by
  funext z
  simp only [put, block, hole]
  split <;> simp_all

theorem put_hole_false (m h g : Int) : put (hole m h) g false = holes m g h := by
  funext z
  simp only [put, hole, holes]
  split <;> simp_all

theorem put_holes_right_true (m g h : Int) (h0 : 0 ≤ h) (hm : h < m) (gh : g ≠ h) :
    put (holes m g h) h true = hole m g := by
  funext z
  simp only [put, hole, holes]
  split <;> simp_all <;> omega

theorem put_holes_left_true (m g h : Int) (h0 : 0 ≤ g) (hm : g < m) (gh : g ≠ h) :
    put (holes m g h) g true = hole m h := by
  funext z
  simp only [put, hole, holes]
  split <;> simp_all

theorem holes_comm (m g h : Int) : holes m g h = holes m h g := by
  funext z
  simp [holes, and_left_comm, and_comm, and_assoc]

theorem scan_right (q : State) (hd : delta q true = ⟨true, .R, some q⟩)
    (t : Tape) (x : Int) (n : Nat) (hs : ∀ j : Nat, j < n → t (x+j) = true) :
    run delta n (cfg q x t) = cfg q (x+n) t := by
  induction n generalizing x with
  | zero => simp [run, cfg]
  | succ n ih =>
    have hx : t x = true := by simpa using hs 0 (by omega)
    have he : step delta (cfg q x t) = cfg q (x+1) t := by
      simp [step, cfg, hx, hd, move, put_same t x true hx]
    rw [run, he, ih]
    · congr 1; omega
    · intro j hj
      have := hs (j+1) (by omega)
      have he : x+1+(j : Int) = x+(j+1 : Nat) := by omega
      rw [he]
      exact this

theorem scan_left (q : State) (hd : delta q true = ⟨true, .L, some q⟩)
    (t : Tape) (x : Int) (n : Nat) (hs : ∀ j : Nat, j < n → t (x-j) = true) :
    run delta n (cfg q x t) = cfg q (x-n) t := by
  induction n generalizing x with
  | zero => simp [run, cfg]
  | succ n ih =>
    have hx : t x = true := by simpa using hs 0 (by omega)
    have he : step delta (cfg q x t) = cfg q (x-1) t := by
      simp [step, cfg, hx, hd, move, put_same t x true hx]
      omega
    rw [run, he, ih]
    · congr 1; omega
    · intro j hj
      have := hs (j+1) (by omega)
      have he : x-1-(j : Int) = x-(j+1 : Nat) := by omega
      rw [he]
      exact this

theorem step_rch (a : Config State) : Rch a (step delta a) := ⟨1, rfl⟩

theorem Rch.of_step {a b : Config State} (h : step delta a = b) : Rch a b :=
  ⟨1, by simpa [run] using h⟩

theorem canonical_finite (M v : Nat) : FiniteTape (canonical M v).tape := by
  refine ⟨0, M, ?_⟩
  intro z hz
  simp only [canonical, hole, decide_eq_false_iff_not]
  omega

theorem init : run delta 4 blank = canonical 2 2 := by
  simp [run, step, blank, canonical, delta, move, put]
  funext z
  by_cases h : z = 0
  · subst z; simp [put, hole]
  · have hn : ¬ (0 ≤ z ∧ z < 2 ∧ z ≠ 1) := by omega
    simp [put, hole, h, hn]

theorem right_to (q : State) (hd : delta q true = ⟨true, .R, some q⟩)
    (t : Tape) (x y : Int) (hxy : x ≤ y)
    (hs : ∀ z, x ≤ z → z < y → t z = true) :
    Rch (cfg q x t) (cfg q y t) := by
  refine ⟨(y-x).toNat, ?_⟩
  have hc : ((y-x).toNat : Int) = y-x := Int.toNat_of_nonneg (by omega)
  have hh := scan_right q hd t x (y-x).toNat (by
    intro j hj
    apply hs <;> omega)
  have he : x+((y-x).toNat : Int) = y := by omega
  rw [he] at hh
  exact hh

theorem left_to (q : State) (hd : delta q true = ⟨true, .L, some q⟩)
    (t : Tape) (x y : Int) (hxy : y ≤ x)
    (hs : ∀ z, y < z → z ≤ x → t z = true) :
    Rch (cfg q x t) (cfg q y t) := by
  refine ⟨(x-y).toNat, ?_⟩
  have hc : ((x-y).toNat : Int) = x-y := Int.toNat_of_nonneg (by omega)
  have hh := scan_left q hd t x (x-y).toNat (by
    intro j hj
    apply hs <;> omega)
  have he : x-((x-y).toNat : Int) = y := by omega
  rw [he] at hh
  exact hh

theorem home (m h x : Int) (hh : 0 ≤ h) (hm : h < m)
    (hx0 : -1 ≤ x) (hxh : x < h) :
    Rch (cfg .C x (hole m h)) (cfg .D 0 (hole m h)) := by
  have hs : Rch (cfg .C x (hole m h)) (cfg .C (-1) (hole m h)) := by
    apply left_to .C rfl _ _ _ hx0
    intro z hz hz'
    simp only [hole, decide_eq_true_eq]
    omega
  apply hs.trans
  refine ⟨1, ?_⟩
  have ht : hole m h (-1) = false := by simp [hole]
  simp [run, step, cfg, ht, delta, move, put_same _ _ _ ht]

theorem home_block (m x : Int) (hm : 0 ≤ m) (hx0 : -1 ≤ x) (hxm : x < m) :
    Rch (cfg .C x (block m)) (cfg .D 0 (block m)) := by
  have hs : Rch (cfg .C x (block m)) (cfg .C (-1) (block m)) := by
    apply left_to .C rfl _ _ _ hx0
    intro z hz hz'
    simp only [block, decide_eq_true_eq]
    omega
  apply hs.trans
  refine ⟨1, ?_⟩
  have ht : block m (-1) = false := by simp [block]
  simp [run, step, cfg, ht, delta, move, put_same _ _ _ ht]

theorem grow (m x : Int) (hm : 0 ≤ m) (hx0 : 0 ≤ x) (hxm : x ≤ m) :
    Rch (cfg .P x (block m)) (cfg .D 0 (block m)) := by
  have hs : Rch (cfg .P x (block m)) (cfg .P m (block m)) := by
    apply right_to .P rfl _ _ _ hxm
    intro z hz hz'
    simp only [block, decide_eq_true_eq]
    omega
  apply hs.trans
  have ht : block m m = false := by simp [block]
  have hstep : step delta (cfg .P m (block m)) = cfg .C (m-1) (block m) := by
    simp [step, cfg, ht, delta, move, put_same _ _ _ ht]
    omega
  exact (Rch.of_step hstep).trans (home_block m (m-1) hm (by omega) (by omega))

theorem block_eq_next_hole (m : Int) : block m = hole (m+1) m := by
  funext z
  simp only [block, hole]
  by_cases hz : 0 ≤ z ∧ z < m
  · have he : 0 ≤ z ∧ z < m+1 ∧ z ≠ m := by omega
    simp [hz, he]
  · have he : ¬ (0 ≤ z ∧ z < m+1 ∧ z ≠ m) := by omega
    simp [hz, he]

theorem reset (M : Nat) (hm : 2 ≤ M) :
    ∃ n, Reaches delta n (canonical M 1) (canonical (M+1) (M+1)) := by
  apply Rch.exact _ (by simp [canonical])
  have ht : hole (M : Int) 0 0 = false := by simp [hole]
  have he : step delta (canonical M 1) = cfg .P 1 (block M) := by
    simp [canonical, step, cfg, ht, delta, move,
      put_hole_true (M : Int) 0 (by omega) (by omega)]
  have hn : cfg .D 0 (block M) = canonical (M+1) (M+1) := by
    simp [canonical, cfg, block_eq_next_hole, Int.natCast_add]
  exact (Rch.of_step he).trans (by
    rw [← hn]
    exact grow M 1 (by omega) (by omega) (by omega))

end CollatzTM.M16
