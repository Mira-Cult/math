import Shared.Beeping.BinarySourceCompiler

/-! Proofs for the left and right branches of the unified finite source-table
compiler. All event flags come from the selected literal source row. -/
namespace Shared.Beeping.BinarySourceMovement
open Shared.Beeping.Machines
open Shared.Beeping.ComparisonAlphabetBits Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.BinarySourceCompiler

def leftConfig {m : Nat} (q : Fin m) (n : Fin 26) (tape : Int → Bool) (head : Int) : Config (Total m) :=
  ⟨pack q (left n),head,tape⟩

theorem left_row_more {m : Nat} (tab : SourceTable m) (q : Fin m) (n : Nat) (hn : n < 24) (b : Bool) :
    row tab (pack q (left ⟨n+2,by omega⟩)) b = ⟨b,.left,pack q (left ⟨n+1,by omega⟩),false⟩ := by
  let p := left ⟨n+2,by omega⟩
  have h1 : ¬p.val < 8192 := by change ¬147456+(n+2) < 8192; omega
  have h2 : ¬p.val < 16384 := by change ¬147456+(n+2) < 16384; omega
  have h3 : ¬p.val < 147456 := by change ¬147456+(n+2) < 147456; omega
  have h4 : p.val < 147482 := by change 147456+(n+2) < 147482; omega
  have h5 : ¬p.val ≤ 147457 := by change ¬147456+(n+2) ≤ 147457; omega
  change row tab (pack q p) b = _
  simp only [row,source_pack,slot_pack,dif_neg h1,dif_neg h2,dif_neg h3,dif_pos h4,if_neg h5]
  congr 1

theorem left_row_last {m : Nat} (tab : SourceTable m) (q : Fin m) (b : Bool) :
    row tab (pack q (left ⟨1,by decide⟩)) b = ⟨b,.left,pack q ready,false⟩ := by
  simp [row,source_pack,slot_pack,left]

theorem right_row {m : Nat} (tab : SourceTable m) (q : Fin m) (b : Bool) :
    row tab (pack q right) b = ⟨b,.right,pack q ready,false⟩ := by
  simp [row,source_pack,slot_pack,right]

theorem left_step_more {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (n : Nat) (hn : n < 24) (tape : Int → Bool) (head : Int) :
    (machine tab start).step (leftConfig q ⟨n+2,by omega⟩ tape head) =
      (leftConfig q ⟨n+1,by omega⟩ tape (head-1),false) := by
  unfold Machine.step
  simp only [leftConfig]
  rw [table_row,left_row_more tab q n hn]
  simp [Move.apply]
  funext i
  by_cases hi : i = head <;> simp [Config.write,hi]

theorem left_step_last {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Bool) (head : Int) :
    (machine tab start).step (leftConfig q ⟨1,by decide⟩ tape head) =
      (⟨pack q ready,head-1,tape⟩,false) := by
  unfold Machine.step
  simp only [leftConfig]
  rw [table_row,left_row_last]
  simp [Move.apply]
  funext i
  by_cases hi : i = head <;> simp [Config.write,hi]

theorem right_step {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Bool) (head : Int) :
    (machine tab start).step ⟨pack q right,head,tape⟩ = (⟨pack q ready,head+1,tape⟩,false) := by
  unfold Machine.step
  rw [table_row,right_row]
  simp [Move.apply]
  funext i
  by_cases hi : i = head <;> simp [Config.write,hi]

/-- Before the last left move, the finite countdown and head position agree. -/
theorem left_prefix {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (n k : Nat) (hn : n ≤ 25) (hk : k < n) (tape : Int → Bool) (head : Int) :
    (machine tab start).system.advance (leftConfig q ⟨n,by omega⟩ tape head) k =
      leftConfig q ⟨n-k,by omega⟩ tape (head-k) := by
  induction k with
  | zero => simp [EventSystem.advance]
  | succ k ih =>
    have hp : k < n := by omega
    change ((machine tab start).step ((machine tab start).system.advance
      (leftConfig q ⟨n,by omega⟩ tape head) k)).1 = _
    rw [ih hp]
    have he : (⟨n-k,by omega⟩ : Fin 26) = ⟨(n-k-2)+2,by omega⟩ := by apply Fin.ext; simp; omega
    rw [he,left_step_more tab start q (n-k-2) (by omega)]
    have hidx : (⟨(n-k-2)+1,by omega⟩ : Fin 26) = ⟨n-(k+1),by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hidx]
    congr 1 <;> simp [leftConfig] <;> omega

theorem dispatch_left {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int)
    (hact : (selected tab q (tape position)).action = .left) :
    (machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 14 =
      leftConfig (selected tab q (tape position)).next ⟨25,by decide⟩ (binaryTape tape) (13*position+12) := by
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 13)).1 = _
  rw [dispatch_transition tab start q tape position]
  simp [hact,dispatchSlot,leftConfig]

theorem dispatch_right {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int)
    (hact : (selected tab q (tape position)).action = .right) :
    (machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 14 =
      ⟨pack (selected tab q (tape position)).next right,13*position+12,binaryTape tape⟩ := by
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 13)).1 = _
  rw [dispatch_transition tab start q tape position]
  simp [hact,dispatchSlot]

theorem complete_left {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int)
    (hact : (selected tab q (tape position)).action = .left) :
    (machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 39 =
      ⟨pack (selected tab q (tape position)).next ready,13*position-13,binaryTape tape⟩ := by
  have h38 : (machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 38 =
      leftConfig (selected tab q (tape position)).next ⟨1,by decide⟩ (binaryTape tape) (13*position-12) := by
    rw [show 38 = 14+24 by decide,BinaryReadWrite.advance_add,dispatch_left tab start q tape position hact,
      left_prefix tab start _ 25 24 (by decide) (by decide)]
    simp [leftConfig]
    omega
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 38)).1 = _
  rw [h38,left_step_last]
  simp only [Prod.fst]
  have he : 13*position-12-1 = 13*position-13 := by omega
  rw [he]

theorem complete_right {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int)
    (hact : (selected tab q (tape position)).action = .right) :
    (machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 15 =
      ⟨pack (selected tab q (tape position)).next ready,13*position+13,binaryTape tape⟩ := by
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 14)).1 = _
  rw [dispatch_right tab start q tape position hact,right_step]
  simp only [Prod.fst]
  have he : 13*position+12+1 = 13*position+13 := by omega
  rw [he]

theorem left_row_silent {m : Nat} (tab : SourceTable m) (q : Fin m) (n : Fin 26) (b : Bool) :
    (row tab (pack q (left n)) b).beep = false := by
  have h1 : ¬(left n).val < 8192 := by change ¬147456+n.val < 8192; omega
  have h2 : ¬(left n).val < 16384 := by change ¬147456+n.val < 16384; omega
  have h3 : ¬(left n).val < 147456 := by change ¬147456+n.val < 147456; omega
  have h4 : (left n).val < 147482 := by change 147456+n.val < 147482; have := n.isLt; omega
  simp only [row,source_pack,slot_pack,dif_neg h1,dif_neg h2,dif_neg h3,dif_pos h4]
  split_ifs <;> rfl

theorem left_phase_silent {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int)
    (hact : (selected tab q (tape position)).action = .left) (k : Nat) (hk : k < 25) :
    ¬ (machine tab start).system.BeepFrom (begin q (binaryTape tape) (13*position)) (14+k) := by
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) (14+k))).2 ≠ true
  rw [BinaryReadWrite.advance_add,dispatch_left tab start q tape position hact,
    left_prefix tab start _ 25 k (by decide) hk]
  change ((machine tab start).table.row _ _).beep ≠ true
  simp only [leftConfig]
  rw [table_row,left_row_silent]
  decide

theorem right_phase_silent {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int)
    (hact : (selected tab q (tape position)).action = .right) :
    ¬ (machine tab start).system.BeepFrom (begin q (binaryTape tape) (13*position)) 14 := by
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 14)).2 ≠ true
  rw [dispatch_right tab start q tape position hact,right_step]
  simp

/-- The 39-step left segment contains exactly the source row's event. -/
theorem left_trace {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int)
    (hact : (selected tab q (tape position)).action = .left) (k : Nat) (hk : k < 39) :
    (machine tab start).system.BeepFrom (begin q (binaryTape tape) (13*position)) k ↔
      k = 13 ∧ (selected tab q (tape position)).beep = true := by
  constructor
  · intro h
    by_cases hpre : k < 13
    · exact False.elim (before_dispatch_silent tab start q (binaryTape tape) (13*position) k hpre h)
    · by_cases hd : k = 13
      · exact ⟨hd,(dispatch_event tab start q tape position).1 (hd ▸ h)⟩
      · have he : k = 14+(k-14) := by omega
        rw [he] at h
        exact False.elim (left_phase_silent tab start q tape position hact (k-14) (by omega) h)
  · rintro ⟨rfl,h⟩
    exact (dispatch_event tab start q tape position).2 h

/-- The 15-step right segment contains exactly the source row's event. -/
theorem right_trace {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int)
    (hact : (selected tab q (tape position)).action = .right) (k : Nat) (hk : k < 15) :
    (machine tab start).system.BeepFrom (begin q (binaryTape tape) (13*position)) k ↔
      k = 13 ∧ (selected tab q (tape position)).beep = true := by
  constructor
  · intro h
    by_cases hpre : k < 13
    · exact False.elim (before_dispatch_silent tab start q (binaryTape tape) (13*position) k hpre h)
    · by_cases hd : k = 13
      · exact ⟨hd,(dispatch_event tab start q tape position).1 (hd ▸ h)⟩
      · have he : k = 14 := by omega
        subst k
        exact False.elim (right_phase_silent tab start q tape position hact h)
  · rintro ⟨rfl,h⟩
    exact (dispatch_event tab start q tape position).2 h

end Shared.Beeping.BinarySourceMovement
