import Shared.Beeping.BinaryBlockWrite

/-! A single finite binary table joins the 13-step scanner to the 15-step
writer. The leaf row computes a finite-alphabet output and event flag from
its decoded input, then performs the writer's first left move. Inputs `f` and
`emit` must be supplied by a later finite source table; an arbitrary Lean
function is not an effective source-table certificate. -/
namespace Shared.Beeping.BinaryReadWrite
open Shared.Beeping.Machines
open Shared.Beeping.ComparisonAlphabetBits Shared.Beeping.ComparisonSingleTape

abbrev N := 147456

def scanState (q : Fin 16384) : Fin N := ⟨q.val,by have := q.isLt; dsimp [N]; omega⟩
def writeState (q : Fin 131072) : Fin N := ⟨16384+q.val,by have := q.isLt; dsimp [N]; omega⟩

def scanConfig (c : Config 16384) : Config N := ⟨scanState c.state,c.head,c.tape⟩
def writeConfig (c : Config 131072) : Config N := ⟨writeState c.state,c.head,c.tape⟩

def row (f : Alphabet → Alphabet) (emit : Alphabet → Bool) (q : Fin N) (read : Bool) : Row N :=
  if h : q.val < 8192 then
    let s : Fin 16384 := ⟨q.val,by omega⟩
    ⟨read,.right,scanState (BinaryBlockScan.next s read),false⟩
  else if h : q.val < 16384 then
    let s : Fin 16384 := ⟨q.val,h⟩
    let a := (BinaryBlockScan.result s).getD default
    let w := BinaryBlockWrite.wordOf (f a)
    ⟨read,.left,writeState (BinaryBlockWrite.state w ⟨1,by decide⟩),emit a⟩
  else
    let s : Fin 131072 := ⟨q.val-16384,by have hq := q.isLt; dsimp [N] at hq; omega⟩
    let r := BinaryBlockWrite.row s read
    ⟨r.write,r.move,writeState r.next,false⟩

def machine (f : Alphabet → Alphabet) (emit : Alphabet → Bool) : Machine N where
  table := ⟨Vector.ofFn fun q => (row f emit q false,row f emit q true)⟩
  start := scanState ⟨1,by decide⟩
  blank := false
  startHead := 0

def begin (tape : Int → Bool) (head : Int) : Config N :=
  scanConfig (BinaryBlockScan.begin tape head)

theorem table_row (f : Alphabet → Alphabet) (emit : Alphabet → Bool) (q : Fin N) (b : Bool) :
    (machine f emit).table.row q b = row f emit q b := by
  cases b <;> simp [machine,Table.row]

theorem scan_row (f : Alphabet → Alphabet) (emit : Alphabet → Bool) (q : Fin 16384)
    (b : Bool) (h : q.val < 8192) :
    row f emit (scanState q) b = ⟨b,.right,scanState (BinaryBlockScan.next q b),false⟩ := by
  simp [row,scanState,h]

theorem writer_row (f : Alphabet → Alphabet) (emit : Alphabet → Bool) (q : Fin 131072) (b : Bool) :
    row f emit (writeState q) b =
      let r := BinaryBlockWrite.row q b
      ⟨r.write,r.move,writeState r.next,false⟩ := by
  have h1 : ¬(writeState q).val < 8192 := by change ¬ 16384+q.val < 8192; omega
  have h2 : ¬(writeState q).val < 16384 := by change ¬ 16384+q.val < 16384; omega
  simp only [row,dif_neg h1,dif_neg h2]
  have he : (⟨(writeState q).val-16384,by have := (writeState q).isLt; dsimp [N] at *; omega⟩ : Fin 131072) = q := by
    apply Fin.ext
    change 16384 + q.val - 16384 = q.val
    omega
  rw [he]

theorem scan_step (f : Alphabet → Alphabet) (emit : Alphabet → Bool) (c : Config 16384)
    (h : c.state.val < 8192) :
    (machine f emit).step (scanConfig c) =
      (scanConfig (BinaryBlockScan.scanner.step c).1,false) := by
  rw [BinaryBlockScan.step]
  simp only [Prod.fst]
  unfold Machine.step
  simp only [scanConfig]
  rw [table_row,scan_row f emit c.state (c.tape c.head) h]
  have hw : (scanConfig c).write (c.tape c.head) = c.tape := by
    funext i
    by_cases hi : i = c.head <;> simp [scanConfig,Config.write,hi]
  simp [scanConfig,Move.apply,hw]
  funext i
  by_cases hi : i = c.head <;> simp [Config.write,hi]

theorem writer_step (f : Alphabet → Alphabet) (emit : Alphabet → Bool) (c : Config 131072) :
    (machine f emit).step (writeConfig c) =
      (writeConfig (BinaryBlockWrite.writer.step c).1,false) := by
  rw [BinaryBlockWrite.step]
  simp only [Prod.fst]
  unfold Machine.step
  simp only [writeConfig]
  rw [table_row,writer_row]
  simp only [writeConfig,Prod.mk.injEq]
  constructor
  · rfl
  · trivial

theorem advance_add {α : Type} (M : EventSystem α) (c : α) (n k : Nat) :
    M.advance c (n+k) = M.advance (M.advance c n) k := by
  induction k with
  | zero => simp [EventSystem.advance]
  | succ k ih =>
    rw [Nat.add_succ,EventSystem.advance,EventSystem.advance,ih]

theorem scan_run (f : Alphabet → Alphabet) (emit : Alphabet → Bool)
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

theorem writer_run (f : Alphabet → Alphabet) (emit : Alphabet → Bool)
    (c : Config 131072) (k : Nat) :
    (machine f emit).system.advance (writeConfig c) k =
      writeConfig (BinaryBlockWrite.writer.system.advance c k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((machine f emit).step ((machine f emit).system.advance (writeConfig c) k)).1 = _
    rw [ih,writer_step]
    rfl

theorem leaf_row (f : Alphabet → Alphabet) (emit : Alphabet → Bool) (q : Fin 16384)
    (a : Alphabet) (b : Bool) (hleaf : 8192 ≤ q.val) (hresult : BinaryBlockScan.result q = some a) :
    row f emit (scanState q) b =
      ⟨b,.left,writeState (BinaryBlockWrite.state (BinaryBlockWrite.wordOf (f a)) ⟨1,by decide⟩),emit a⟩ := by
  have h1 : ¬(scanState q).val < 8192 := by change ¬q.val < 8192; omega
  have h2 : (scanState q).val < 16384 := by exact q.isLt
  simp only [row,dif_neg h1,dif_pos h2]
  have he : (⟨(scanState q).val,h2⟩ : Fin 16384) = q := by apply Fin.ext; rfl
  rw [he,hresult]
  rfl

theorem dispatch (f : Alphabet → Alphabet) (emit : Alphabet → Bool) (c : Config 16384)
    (a : Alphabet) (hleaf : 8192 ≤ c.state.val) (hresult : BinaryBlockScan.result c.state = some a) :
    (machine f emit).step (scanConfig c) =
      (writeConfig ((BinaryBlockWrite.writer.system.advance
        (BinaryBlockWrite.begin (BinaryBlockWrite.wordOf (f a)) c.tape c.head) 1)),emit a) := by
  rw [BinaryBlockWrite.first]
  unfold Machine.step
  simp only [scanConfig]
  rw [table_row,leaf_row f emit c.state a (c.tape c.head) hleaf hresult]
  have hw : (⟨scanState c.state,c.head,c.tape⟩ : Config N).write (c.tape c.head) = c.tape := by
    funext i
    by_cases hi : i = c.head <;> simp [Config.write,hi]
  simp [writeConfig,Move.apply,hw]

/-- The joined table scans the source cell, performs its selected write, and
returns to the aligned boundary in exactly 28 transitions. -/
theorem complete (f : Alphabet → Alphabet) (emit : Alphabet → Bool)
    (tape : Int → Alphabet) (position : Int) :
    (machine f emit).system.advance (begin (binaryTape tape) (13*position)) 28 =
      writeConfig ⟨BinaryBlockWrite.state (BinaryBlockWrite.wordOf (f (tape position))) ⟨15,by decide⟩,
        13*position,binaryTape (Function.update tape position (f (tape position)))⟩ := by
  let c := BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13
  have hs : (machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13 = scanConfig c :=
    scan_run f emit (binaryTape tape) (13*position) 13 (by decide)
  have ⟨hr,hh,ht⟩ := BinaryBlockScan.scan_block tape position
  have hl := BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)
  have h14 : (machine f emit).system.advance (begin (binaryTape tape) (13*position)) 14 =
      writeConfig (BinaryBlockWrite.writer.system.advance
        (BinaryBlockWrite.begin (BinaryBlockWrite.wordOf (f (tape position))) (binaryTape tape) (13*position+13)) 1) := by
    change ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13)).1 = _
    rw [hs,dispatch f emit c (tape position) hl hr]
    simp [c,hh,ht]
  rw [show 28 = 14+14 by decide,advance_add,h14,writer_run,←advance_add]
  simpa using congrArg writeConfig (BinaryBlockWrite.write_binary_cell tape position (f (tape position)))

theorem before_dispatch_silent (f : Alphabet → Alphabet) (emit : Alphabet → Bool)
    (tape : Int → Bool) (head : Int) (k : Nat) (hk : k < 13) :
    ¬ (machine f emit).system.BeepFrom (begin tape head) k := by
  have hs := (BinaryBlockScan.scan tape head k (by omega)).1
  have hl := BinaryBlockScan.index_live tape head k hk
  change ((machine f emit).step ((machine f emit).system.advance (begin tape head) k)).2 ≠ true
  rw [scan_run f emit tape head k (by omega),scan_step f emit _ (by simpa [hs] using hl)]
  simp

theorem dispatch_event (f : Alphabet → Alphabet) (emit : Alphabet → Bool)
    (tape : Int → Alphabet) (position : Int) :
    (machine f emit).system.BeepFrom (begin (binaryTape tape) (13*position)) 13 ↔
      emit (tape position) = true := by
  let c := BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13
  have hr := (BinaryBlockScan.scan_block tape position).1
  have hl := BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)
  change ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13)).2 = true ↔ _
  rw [scan_run f emit (binaryTape tape) (13*position) 13 (by decide),dispatch f emit c (tape position) hl hr]

theorem writer_silent (f : Alphabet → Alphabet) (emit : Alphabet → Bool)
    (c : Config 131072) (k : Nat) :
    ¬ (machine f emit).system.BeepFrom (writeConfig c) k := by
  change ((machine f emit).step ((machine f emit).system.advance (writeConfig c) k)).2 ≠ true
  rw [writer_run,writer_step]
  simp

/-- After the unique dispatch row, the writer phase remains silent forever. -/
theorem after_dispatch_silent (f : Alphabet → Alphabet) (emit : Alphabet → Bool)
    (tape : Int → Alphabet) (position : Int) (k : Nat) :
    ¬ (machine f emit).system.BeepFrom (begin (binaryTape tape) (13*position)) (14+k) := by
  let c := BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13
  have hs : (machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13 = scanConfig c :=
    scan_run f emit (binaryTape tape) (13*position) 13 (by decide)
  have ⟨hr,hh,ht⟩ := BinaryBlockScan.scan_block tape position
  have hl := BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)
  have h14 : (machine f emit).system.advance (begin (binaryTape tape) (13*position)) 14 =
      writeConfig (BinaryBlockWrite.writer.system.advance
        (BinaryBlockWrite.begin (BinaryBlockWrite.wordOf (f (tape position))) (binaryTape tape) (13*position+13)) 1) := by
    change ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) 13)).1 = _
    rw [hs,dispatch f emit c (tape position) hl hr]
    simp [c,hh,ht]
  change ((machine f emit).step ((machine f emit).system.advance (begin (binaryTape tape) (13*position)) (14+k))).2 ≠ true
  rw [advance_add,h14,writer_run,writer_step]
  simp

/-- The entire infinite run has exactly the selected event at transition 13,
or no events when the selected flag is false. -/
theorem beep_exact (f : Alphabet → Alphabet) (emit : Alphabet → Bool)
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

end Shared.Beeping.BinaryReadWrite
