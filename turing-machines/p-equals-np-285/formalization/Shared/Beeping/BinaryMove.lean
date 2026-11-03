import Shared.Beeping.BinaryReadWrite

/-! A concrete binary table implements a post-Turing head move after scanning
one 13-bit cell. It chooses the direction and event from a finite source row.
A later compiler must bind those row functions and restart the next macrostep. -/
namespace Shared.Beeping.BinaryMove
open Shared.Beeping.Machines
open Shared.Beeping.ComparisonAlphabetBits Shared.Beeping.ComparisonSingleTape

abbrev N := 16411

def scanState (q : Fin 16384) : Fin N := ⟨q.val,by have := q.isLt; dsimp [N]; omega⟩
def leftState (q : Fin 26) : Fin N := ⟨16384+q.val,by have := q.isLt; dsimp [N]; omega⟩
def rightState : Fin N := ⟨16410,by decide⟩
def scanConfig (c : Config 16384) : Config N := ⟨scanState c.state,c.head,c.tape⟩
def leftConfig (q : Fin 26) (tape : Int → Bool) (head : Int) : Config N := ⟨leftState q,head,tape⟩

def row (goRight : Alphabet → Bool) (emit : Alphabet → Bool) (q : Fin N) (b : Bool) : Row N :=
  if h : q.val < 8192 then
    let s : Fin 16384 := ⟨q.val,by omega⟩
    ⟨b,.right,scanState (BinaryBlockScan.next s b),false⟩
  else if h : q.val < 16384 then
    let s : Fin 16384 := ⟨q.val,h⟩
    let a := (BinaryBlockScan.result s).getD default
    ⟨b,.left,if goRight a then rightState else leftState ⟨25,by decide⟩,emit a⟩
  else if h : q.val < 16410 then
    if hz : q.val = 16384 then ⟨b,.right,q,false⟩
    else ⟨b,.left,⟨q.val-1,by have hq := q.isLt; dsimp [N] at hq; omega⟩,false⟩
  else ⟨b,.right,leftState ⟨0,by decide⟩,false⟩

def machine (goRight : Alphabet → Bool) (emit : Alphabet → Bool) : Machine N where
  table := ⟨Vector.ofFn fun q => (row goRight emit q false,row goRight emit q true)⟩
  start := scanState ⟨1,by decide⟩
  blank := false
  startHead := 0

def begin (tape : Int → Bool) (head : Int) : Config N := scanConfig (BinaryBlockScan.begin tape head)

theorem table_row (f : Alphabet → Bool) (emit : Alphabet → Bool) (q : Fin N) (b : Bool) :
    (machine f emit).table.row q b = row f emit q b := by
  cases b <;> simp [machine,Table.row]

theorem scan_row (f : Alphabet → Bool) (emit : Alphabet → Bool) (q : Fin 16384)
    (b : Bool) (h : q.val < 8192) :
    row f emit (scanState q) b = ⟨b,.right,scanState (BinaryBlockScan.next q b),false⟩ := by
  simp [row,scanState,h]

theorem scan_step (f : Alphabet → Bool) (emit : Alphabet → Bool) (c : Config 16384)
    (h : c.state.val < 8192) :
    (machine f emit).step (scanConfig c) = (scanConfig (BinaryBlockScan.scanner.step c).1,false) := by
  rw [BinaryBlockScan.step]
  simp only [Prod.fst]
  unfold Machine.step
  simp only [scanConfig]
  rw [table_row,scan_row f emit c.state (c.tape c.head) h]
  simp [scanConfig,Move.apply]
  funext i
  by_cases hi : i = c.head <;> simp [Config.write,hi]

theorem scan_run (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (tape : Int → Bool) (head : Int) (k : Nat) (hk : k ≤ 13) :
    (machine f emit).system.advance (begin tape head) k =
      scanConfig (BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin tape head) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : k ≤ 13 := by omega
    have hs := (BinaryBlockScan.scan tape head k hp).1
    have hl := BinaryBlockScan.index_live tape head k (by omega)
    change ((machine f emit).step ((machine f emit).system.advance (begin tape head) k)).1 = _
    rw [ih hp,scan_step f emit _ (by simpa [hs] using hl)]
    rfl

theorem leaf_row (f : Alphabet → Bool) (emit : Alphabet → Bool) (q : Fin 16384)
    (a : Alphabet) (b : Bool) (hleaf : 8192 ≤ q.val) (hresult : BinaryBlockScan.result q = some a) :
    row f emit (scanState q) b =
      ⟨b,.left,if f a then rightState else leftState ⟨25,by decide⟩,emit a⟩ := by
  have h1 : ¬(scanState q).val < 8192 := by change ¬q.val < 8192; omega
  have h2 : (scanState q).val < 16384 := by exact q.isLt
  simp only [row,dif_neg h1,dif_pos h2]
  have he : (⟨(scanState q).val,h2⟩ : Fin 16384) = q := by apply Fin.ext; rfl
  rw [he,hresult]
  rfl

theorem dispatch (f : Alphabet → Bool) (emit : Alphabet → Bool) (c : Config 16384)
    (a : Alphabet) (hleaf : 8192 ≤ c.state.val) (hresult : BinaryBlockScan.result c.state = some a) :
    (machine f emit).step (scanConfig c) =
      (⟨if f a then rightState else leftState ⟨25,by decide⟩,c.head-1,c.tape⟩,emit a) := by
  unfold Machine.step
  simp only [scanConfig]
  rw [table_row,leaf_row f emit c.state a (c.tape c.head) hleaf hresult]
  simp [Move.apply]
  funext i
  by_cases hi : i = c.head <;> simp [Config.write,hi]

theorem left_row (f : Alphabet → Bool) (emit : Alphabet → Bool) (n : Nat) (hn : n < 25) (b : Bool) :
    row f emit (leftState ⟨n+1,by omega⟩) b = ⟨b,.left,leftState ⟨n,by omega⟩,false⟩ := by
  have h1 : ¬(leftState ⟨n+1,by omega⟩).val < 8192 := by change ¬16384+(n+1) < 8192; omega
  have h2 : ¬(leftState ⟨n+1,by omega⟩).val < 16384 := by change ¬16384+(n+1) < 16384; omega
  have h3 : (leftState ⟨n+1,by omega⟩).val < 16410 := by change 16384+(n+1) < 16410; omega
  have h4 : ¬(leftState ⟨n+1,by omega⟩).val = 16384 := by change ¬16384+(n+1) = 16384; omega
  simp only [row,dif_neg h1,dif_neg h2,dif_pos h3,dif_neg h4]
  congr 1

theorem left_step (f : Alphabet → Bool) (emit : Alphabet → Bool) (n : Nat) (hn : n < 25)
    (tape : Int → Bool) (head : Int) :
    (machine f emit).step (leftConfig ⟨n+1,by omega⟩ tape head) =
      (leftConfig ⟨n,by omega⟩ tape (head-1),false) := by
  unfold Machine.step
  simp only [leftConfig]
  rw [table_row,left_row f emit n hn]
  simp [leftConfig,Move.apply]
  funext i
  by_cases hi : i = head <;> simp [Config.write,hi]

theorem right_step (f : Alphabet → Bool) (emit : Alphabet → Bool) (tape : Int → Bool) (head : Int) :
    (machine f emit).step ⟨rightState,head,tape⟩ = (leftConfig ⟨0,by decide⟩ tape (head+1),false) := by
  unfold Machine.step
  rw [table_row]
  simp [row,rightState,leftConfig,leftState,Move.apply]
  funext i
  by_cases hi : i = head <;> simp [Config.write,hi]

/-- A countdown of `n` states executes exactly `n` left moves. -/
theorem left_run (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (n : Nat) (hn : n ≤ 25) (tape : Int → Bool) (head : Int) :
    (machine f emit).system.advance (leftConfig ⟨n,by omega⟩ tape head) n =
      leftConfig ⟨0,by decide⟩ tape (head-n) := by
  induction n generalizing head with
  | zero => simp [EventSystem.advance]
  | succ n ih =>
    have hn' : n < 25 := by omega
    have hadv := BinaryReadWrite.advance_add (machine f emit).system
      (leftConfig ⟨n+1,by omega⟩ tape head) 1 n
    simp only [Nat.one_add] at hadv
    rw [hadv]
    change (machine f emit).system.advance ((machine f emit).step
      (leftConfig ⟨n+1,by omega⟩ tape head)).1 n = _
    rw [left_step f emit n hn',ih (by omega) (head-1)]
    congr 1 <;> simp [leftConfig] <;> omega

/-- Both directions select the row using the original cell. A right move takes
15 transitions; a left move takes 39. The tape is unchanged. -/
theorem complete (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (tape : Int → Alphabet) (position : Int) :
    (machine f emit).system.advance (begin (binaryTape tape) (13*position))
      (if f (tape position) then 15 else 39) =
      leftConfig ⟨0,by decide⟩ (binaryTape tape)
        (if f (tape position) then 13*position+13 else 13*position-13) := by
  let c := BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13
  have hs : (machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13 = scanConfig c :=
    scan_run f emit (binaryTape tape) (13*position) 13 (by decide)
  have ⟨hr,hh,ht⟩ := BinaryBlockScan.scan_block tape position
  have hl := BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)
  have h14 : (machine f emit).system.advance (begin (binaryTape tape) (13*position)) 14 =
      ⟨if f (tape position) then rightState else leftState ⟨25,by decide⟩,
        13*position+12,binaryTape tape⟩ := by
    change ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13)).1 = _
    rw [hs,dispatch f emit c (tape position) hl hr]
    simp [c,hh,ht]
    omega
  cases hf : f (tape position) with
  | false =>
    simp only [hf,Bool.false_eq_true,↓reduceIte] at h14 ⊢
    rw [show 39 = 14+25 by decide,BinaryReadWrite.advance_add,h14]
    change (machine f emit).system.advance (leftConfig ⟨25,by decide⟩ (binaryTape tape) (13*position+12)) 25 = _
    rw [left_run f emit 25 (by decide)]
    congr 1 <;> simp [leftConfig] <;> omega
  | true =>
    simp only [hf,↓reduceIte] at h14 ⊢
    change ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) 14)).1 = _
    rw [h14,right_step]
    congr 1 <;> simp [leftConfig] <;> omega

/-- The completed right-move configuration encodes the actual post-Turing
tape relative to its new head. -/
theorem complete_right_postTape (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (tape : Turing.Tape Alphabet) (h : f tape.head = true) :
    let c := (machine f emit).system.advance (begin (binaryTape tape.nth) 0) 15
    c.head = 13 ∧ ∀ i, c.tape (c.head+i) = binaryTape (tape.move Turing.Dir.right).nth i := by
  have hc := complete f emit tape.nth 0
  simp only [Int.mul_zero,Turing.Tape.nth_zero,h,↓reduceIte,Int.zero_add] at hc
  rw [hc]
  constructor
  · rfl
  · intro i
    simp only [leftConfig]
    rw [ComparisonAlphabetBits.move_right_binary]
    congr 1 <;> omega

/-- The completed left-move configuration encodes the actual post-Turing
tape relative to its new head. -/
theorem complete_left_postTape (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (tape : Turing.Tape Alphabet) (h : f tape.head = false) :
    let c := (machine f emit).system.advance (begin (binaryTape tape.nth) 0) 39
    c.head = -13 ∧ ∀ i, c.tape (c.head+i) = binaryTape (tape.move Turing.Dir.left).nth i := by
  have hc := complete f emit tape.nth 0
  simp only [Int.mul_zero,Turing.Tape.nth_zero,h,Bool.false_eq_true,↓reduceIte,Int.zero_sub] at hc
  rw [hc]
  constructor
  · rfl
  · intro i
    simp only [leftConfig]
    rw [ComparisonAlphabetBits.move_left_binary]
    congr 1 <;> omega

/-- Every movement-phase row is silent and stays in the movement phase. -/
theorem tail_row (f : Alphabet → Bool) (emit : Alphabet → Bool) (q : Fin N) (b : Bool)
    (h : 16384 ≤ q.val) : (row f emit q b).beep = false ∧ 16384 ≤ (row f emit q b).next.val := by
  have h1 : ¬q.val < 8192 := by omega
  have h2 : ¬q.val < 16384 := by omega
  simp only [row,dif_neg h1,dif_neg h2]
  split_ifs <;> simp [leftState] <;> omega

theorem tail_state (f : Alphabet → Bool) (emit : Alphabet → Bool) (c : Config N)
    (h : 16384 ≤ c.state.val) (k : Nat) :
    16384 ≤ ((machine f emit).system.advance c k).state.val := by
  induction k with
  | zero => exact h
  | succ k ih =>
    change 16384 ≤ ((machine f emit).step ((machine f emit).system.advance c k)).1.state.val
    change 16384 ≤ ((machine f emit).table.row _ _).next.val
    rw [table_row]
    exact (tail_row f emit _ _ ih).2

theorem tail_silent (f : Alphabet → Bool) (emit : Alphabet → Bool) (c : Config N)
    (h : 16384 ≤ c.state.val) (k : Nat) :
    ¬ (machine f emit).system.BeepFrom c k := by
  have hs := tail_state f emit c h k
  change ((machine f emit).step ((machine f emit).system.advance c k)).2 ≠ true
  change ((machine f emit).table.row _ _).beep ≠ true
  rw [table_row,(tail_row f emit _ _ hs).1]
  decide

theorem before_dispatch_silent (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (tape : Int → Bool) (head : Int) (k : Nat) (hk : k < 13) :
    ¬ (machine f emit).system.BeepFrom (begin tape head) k := by
  have hs := (BinaryBlockScan.scan tape head k (by omega)).1
  have hl := BinaryBlockScan.index_live tape head k hk
  change ((machine f emit).step ((machine f emit).system.advance (begin tape head) k)).2 ≠ true
  rw [scan_run f emit tape head k (by omega),scan_step f emit _ (by simpa [hs] using hl)]
  simp

theorem dispatch_event (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (tape : Int → Alphabet) (position : Int) :
    (machine f emit).system.BeepFrom (begin (binaryTape tape) (13*position)) 13 ↔
      emit (tape position) = true := by
  let c := BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13
  have hr := (BinaryBlockScan.scan_block tape position).1
  have hl := BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)
  change ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13)).2 = true ↔ _
  rw [scan_run f emit (binaryTape tape) (13*position) 13 (by decide),dispatch f emit c (tape position) hl hr]

theorem after_dispatch_silent (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (tape : Int → Alphabet) (position : Int) (k : Nat) :
    ¬ (machine f emit).system.BeepFrom (begin (binaryTape tape) (13*position)) (14+k) := by
  let c := BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13
  have hs : (machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13 = scanConfig c :=
    scan_run f emit (binaryTape tape) (13*position) 13 (by decide)
  have hr := (BinaryBlockScan.scan_block tape position).1
  have hl := BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)
  have h14 : 16384 ≤ ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) 14).state.val := by
    change 16384 ≤ ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13)).1.state.val
    rw [hs,dispatch f emit c (tape position) hl hr]
    cases f (tape position) <;> simp [rightState,leftState]
  change ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) (14+k))).2 ≠ true
  rw [BinaryReadWrite.advance_add]
  exact tail_silent f emit _ h14 k

theorem beep_exact (f : Alphabet → Bool) (emit : Alphabet → Bool)
    (tape : Int → Alphabet) (position : Int) (k : Nat) :
    (machine f emit).system.BeepFrom (begin (binaryTape tape) (13*position)) k ↔
      k = 13 ∧ emit (tape position) = true := by
  constructor
  · intro h
    by_cases ht : k < 13
    · exact False.elim (before_dispatch_silent f emit (binaryTape tape) (13*position) k ht h)
    · by_cases he : k = 13
      · exact ⟨he,(dispatch_event f emit tape position).1 (he ▸ h)⟩
      · have hk : k = 14 + (k-14) := by omega
        rw [hk] at h
        exact False.elim (after_dispatch_silent f emit tape position (k-14) h)
  · rintro ⟨rfl,h⟩
    exact (dispatch_event f emit tape position).2 h

end Shared.Beeping.BinaryMove
