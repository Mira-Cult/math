import CollatzTM.Arithmetic

namespace CollatzTM.Arithmetic

theorem iterate_zero (f : Nat → Nat) (n : Nat) : iterate f 0 n = n := rfl

theorem iterate_succ (f : Nat → Nat) (k n : Nat) :
    iterate f (k+1) n = f (iterate f k n) := rfl

theorem iterate_add (f : Nat → Nat) (a b n : Nat) :
    iterate f (a+b) n = iterate f a (iterate f b n) := by
  induction a with
  | zero => simp [iterate]
  | succ a ih => rw [Nat.add_right_comm, iterate_succ, iterate_succ, ih]

theorem iterate_succ' (f : Nat → Nat) (k n : Nat) :
    iterate f (k+1) n = iterate f k (f n) := by
  rw [iterate_add]; rfl

theorem ordinary_even (n : Nat) (h : n % 2 = 0) : ordinary n = n/2 := by
  simp [ordinary,h]

theorem ordinary_odd (n : Nat) (h : n % 2 ≠ 0) : ordinary n = 3*n+1 := by
  simp [ordinary,h]

theorem ordinary_pos (n : Nat) (h : 0 < n) : 0 < ordinary n := by
  unfold ordinary; split <;> omega

theorem ordinary_odd_even (n : Nat) (h : n % 2 ≠ 0) :
    (3*n+1)%2 = 0 := by omega

/-- Every shortcut step expands to one or two ordinary steps. -/
theorem shortcut_expands (n : Nat) :
    ∃ k, 0 < k ∧ iterate ordinary k n = shortcut n := by
  by_cases h : n%2=0
  · exact ⟨1, by decide, by simp [iterate, ordinary, shortcut, h]⟩
  · refine ⟨2, by decide, ?_⟩
    simp [iterate,ordinary_odd n h,ordinary_even _ (ordinary_odd_even n h),shortcut_odd n (by omega)]

/-- A positive shortcut path expands to a positive ordinary path. -/
theorem shortcut_path_expands (k n : Nat) :
    ∃ j, (0 < k → 0 < j) ∧ uit j n = sit k n := by
  induction k with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    obtain ⟨j,hj,e⟩ := ih
    obtain ⟨r,hr,er⟩ := shortcut_expands (sit k n)
    refine ⟨r+j, by omega, ?_⟩
    change iterate ordinary (r+j) n = shortcut (sit k n)
    rw [iterate_add]
    change iterate ordinary j n = sit k n at e
    rw [e,er]

/-- Ordinary paths ending at an odd number can be compressed, since inserted
    intermediate values `3n+1` are even. -/
theorem ordinary_path_compresses_odd (k : Nat) :
    ∀ n m, m%2=1 → uit k n=m → ∃ j, (0<k → 0<j) ∧ sit j n=m := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro n m hm he
    cases k with
    | zero => exact ⟨0, by omega, he⟩
    | succ k =>
      by_cases hn : n%2=0
      · have e : uit k (ordinary n)=m := by
          change iterate ordinary k (ordinary n)=m
          rw [← iterate_succ']; exact he
        obtain ⟨j,hj,ej⟩ := ih k (by omega) (ordinary n) m hm e
        refine ⟨j+1, by omega, ?_⟩
        change iterate shortcut (j+1) n=m
        rw [iterate_succ']
        have ee : shortcut n=ordinary n := by simp [shortcut,ordinary,hn]
        rw [ee]; exact ej
      · cases k with
        | zero =>
          have he' : 3*n+1=m := by simpa [uit,iterate,ordinary,hn] using he
          have := ordinary_odd_even n hn
          omega
        | succ k =>
          have e : uit k (ordinary (ordinary n))=m := by
            change iterate ordinary k (ordinary (ordinary n))=m
            rw [← iterate_succ', ← iterate_succ']; exact he
          have ee : ordinary (ordinary n)=shortcut n := by
            rw [ordinary_odd n hn, ordinary_even _ (ordinary_odd_even n hn),shortcut_odd n (by omega)]
          rw [ee] at e
          obtain ⟨j,hj,ej⟩ := ih k (by omega) (shortcut n) m hm e
          refine ⟨j+1, by omega, ?_⟩
          change iterate shortcut (j+1) n=m
          rw [iterate_succ']; exact ej

theorem reaches_one_iff (n : Nat) :
    (∃ k, sit k n=1) ↔ ∃ k, uit k n=1 := by
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨j,_,e⟩ := shortcut_path_expands k n
    exact ⟨j,e.trans hk⟩
  · rintro ⟨k,hk⟩
    obtain ⟨j,_,e⟩ := ordinary_path_compresses_odd k n 1 (by decide) hk
    exact ⟨j,e⟩

def OrdinaryCounter : Prop :=
  ∃ n k, 0<n ∧ 0<k ∧ uit k n=n ∧ n≠1 ∧ n≠2 ∧ n≠4

/-- The complete ordinary orbit of 1 lies in its familiar three-cycle. -/
theorem ordinary_orbit_one (k : Nat) :
    uit k 1=1 ∨ uit k 1=2 ∨ uit k 1=4 := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    change ordinary (uit k 1)=1 ∨ ordinary (uit k 1)=2 ∨ ordinary (uit k 1)=4
    rcases ih with h | h | h <;> rw [h] <;> decide

/-- Every point of an ordinary periodic orbit is periodic with the same period. -/
theorem ordinary_periodic_shift (n k j : Nat) (h : uit k n=n) :
    uit k (uit j n)=uit j n := by
  change iterate ordinary k (iterate ordinary j n)=iterate ordinary j n
  change iterate ordinary k n = n at h
  rw [← iterate_add, Nat.add_comm,iterate_add,h]

/-- A periodic orbit not equal to the trivial cycle cannot visit 1. -/
theorem ordinary_counter_avoids_one (n k : Nat) (hk : 0<k) (hp : uit k n=n)
    (h1 : n≠1) (h2 : n≠2) (h4 : n≠4) : ∀ j, uit j n≠1 := by
  intro j hj
  have ep : ∀ q, uit (j%k+k*q) n=uit (j%k) n := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [Nat.mul_succ,← Nat.add_assoc]
      change iterate ordinary (j%k+k*q+k) n=_
      change iterate ordinary k n=n at hp
      rw [iterate_add,hp]
      exact ih
  have hj' : uit (j%k) n=1 := by
    rw [← ep (j/k),Nat.mod_add_div]; exact hj
  have he : uit (k-j%k) (uit (j%k) n)=n := by
    change iterate ordinary (k-j%k) (iterate ordinary (j%k) n)=n
    rw [← iterate_add, show k-j%k+j%k=k by have := Nat.mod_lt j hk; omega]
    exact hp
  rw [hj'] at he
  rcases ordinary_orbit_one (k-j%k) with e | e | e <;> omega

/-- Hence all points of a nontrivial ordinary periodic orbit avoid 1,2,4. -/
theorem ordinary_counter_avoids_trivial (n k : Nat) (hk : 0<k) (hp : uit k n=n)
    (h1 : n≠1) (h2 : n≠2) (h4 : n≠4) (j : Nat) :
    uit j n≠1 ∧ uit j n≠2 ∧ uit j n≠4 := by
  have ha := ordinary_counter_avoids_one n k hk hp h1 h2 h4
  refine ⟨ha j,?_,?_⟩
  · intro he
    have hh := ha (j+1)
    change ordinary (uit j n)≠1 at hh
    rw [he] at hh
    exact hh (by decide)
  · intro he
    have hh := ha (j+2)
    change ordinary (ordinary (uit j n))≠1 at hh
    rw [he] at hh
    exact hh (by decide)

/-- A nontrivial ordinary cycle contains an odd point ≥3. -/
theorem ordinary_counter_odd (h : OrdinaryCounter) :
    ∃ n k, 3≤n ∧ n%2=1 ∧ 0<k ∧ uit k n=n := by
  obtain ⟨n0,k0,hn0,hk0,hp0,h1,h2,h4⟩ := h
  obtain ⟨n,hn,hmin⟩ := first_index (P:=fun n =>
    ∃ k, 0<n ∧ 0<k ∧ uit k n=n ∧ n≠1 ∧ n≠2 ∧ n≠4) ⟨n0,k0,hn0,hk0,hp0,h1,h2,h4⟩
  obtain ⟨k,hn,hk,hp,h1,h2,h4⟩ := hn
  refine ⟨n,k,by omega,?_,hk,hp⟩
  by_cases he : n%2=0
  · have hm := ordinary_counter_avoids_trivial n k hk hp h1 h2 h4 1
    have hp' := ordinary_periodic_shift n k 1 hp
    have hp1 : 0<ordinary n := ordinary_pos n hn
    have hsmall : ordinary n<n := by rw [ordinary_even n he]; omega
    apply False.elim
    apply hmin (ordinary n) hsmall
    exact ⟨k,hp1,hk,hp',hm.1,hm.2.1,hm.2.2⟩
  · omega

theorem ordinary_counter_implies_shortcut (h : OrdinaryCounter) : ShortcutCounter := by
  obtain ⟨n,k,hn,hodd,hk,hp⟩ := ordinary_counter_odd h
  obtain ⟨j,hj,ej⟩ := ordinary_path_compresses_odd k n n hodd hp
  exact ⟨n,j,hn,hj hk,ej⟩

/-- A nontrivial shortcut periodic point cannot be 4: its shortcut orbit is
    `4,2,1,2,1,...`, so it is not periodic. -/
theorem shortcut_four_not_periodic (k : Nat) (hk : 0<k) : sit k 4≠4 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  change iterate shortcut (j+1) 4 ≠ 4
  rw [iterate_succ']
  change sit j 2≠4
  have h : ∀ j, sit j 2=1 ∨ sit j 2=2 := by
    intro j
    induction j with
    | zero => exact Or.inr rfl
    | succ j ih =>
      change shortcut (sit j 2)=1 ∨ shortcut (sit j 2)=2
      rcases ih with h | h <;> rw [h] <;> decide
  have := h j
  omega

theorem shortcut_counter_implies_ordinary (h : ShortcutCounter) : OrdinaryCounter := by
  obtain ⟨n,k,hn,hk,hp⟩ := h
  obtain ⟨j,hj,ej⟩ := shortcut_path_expands k n
  refine ⟨n,j,by omega,hj hk,ej.trans hp,by omega,by omega,?_⟩
  intro he
  subst n
  exact shortcut_four_not_periodic k hk hp

theorem counter_iff : ShortcutCounter ↔ OrdinaryCounter :=
  ⟨shortcut_counter_implies_ordinary,ordinary_counter_implies_shortcut⟩

end CollatzTM.Arithmetic
