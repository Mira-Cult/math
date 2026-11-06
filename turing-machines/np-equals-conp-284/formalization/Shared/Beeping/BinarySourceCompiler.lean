import Shared.Beeping.BinaryMove

/-! Concrete source-table compiler: one finite source row for every source
state and 13-bit input word. The per-source-state binary control has one
scanner, writer phases, and left/right movement phases. This file first proves
the scan and dispatch interface; correctness of complete repeated source
steps and the infinite-run event refinement are further obligations. -/
namespace Shared.Beeping.BinarySourceCompiler
open Shared.Beeping.Machines
open Shared.Beeping.ComparisonAlphabetBits Shared.Beeping.ComparisonSingleTape

inductive Action where
  | write (a : Alphabet)
  | left
  | right

structure SourceRow (m : Nat) where
  next : Fin m
  action : Action
  beep : Bool

/-- A literal finite table: one row per source state and possible 13-bit word.
Malformed words have explicit table entries as well. -/
abbrev SourceTable (m : Nat) := Vector (Vector (SourceRow m) 8192) m

abbrev L := 147483
abbrev Total (m : Nat) := m * L

def pack {m : Nat} (q : Fin m) (p : Fin L) : Fin (Total m) :=
  ⟨q.val*L+p.val, by have hq := q.isLt; have hp := p.isLt; dsimp [Total,L] at *; omega⟩

def source {m : Nat} (q : Fin (Total m)) : Fin m :=
  ⟨q.val/L, by have hq := q.isLt; dsimp [Total,L] at *; omega⟩

def slot {m : Nat} (q : Fin (Total m)) : Fin L :=
  ⟨q.val%L, by dsimp [L]; omega⟩

theorem source_pack {m : Nat} (q : Fin m) (p : Fin L) : source (pack q p) = q := by
  apply Fin.ext
  have hp := p.isLt
  dsimp [source,pack,L] at *
  omega

theorem slot_pack {m : Nat} (q : Fin m) (p : Fin L) : slot (pack q p) = p := by
  apply Fin.ext
  have hp := p.isLt
  dsimp [slot,pack,L] at *
  omega

def scan (q : Fin 16384) : Fin L := ⟨q.val,by have := q.isLt; dsimp [L]; omega⟩
def write (q : Fin 131072) : Fin L := ⟨16384+q.val,by have := q.isLt; dsimp [L]; omega⟩
def left (q : Fin 26) : Fin L := ⟨147456+q.val,by have := q.isLt; dsimp [L]; omega⟩
def right : Fin L := ⟨147482,by decide⟩
def ready : Fin L := scan ⟨1,by decide⟩

/-- All row outputs and flags are fixed by finite `SourceTable` entries.
The scanner uses 13 transitions, then the dispatch row takes one transition.
The final writer or movement row restarts scanning in the destination state. -/
def row {m : Nat} (tab : SourceTable m) (q : Fin (Total m)) (b : Bool) : Row (Total m) :=
  let src := source q
  let p := slot q
  if h : p.val < 8192 then
    let s : Fin 16384 := ⟨p.val,by omega⟩
    ⟨b,.right,pack src (scan (BinaryBlockScan.next s b)),false⟩
  else if h : p.val < 16384 then
    let w : Fin 8192 := ⟨p.val-8192,by omega⟩
    let r := (tab.get src).get w
    match r.action with
    | .write a =>
      ⟨b,.left,pack r.next (write (BinaryBlockWrite.state (BinaryBlockWrite.wordOf a) ⟨1,by decide⟩)),r.beep⟩
    | .left => ⟨b,.left,pack r.next (left ⟨25,by decide⟩),r.beep⟩
    | .right => ⟨b,.left,pack r.next right,r.beep⟩
  else if h : p.val < 147456 then
    let w : Fin 131072 := ⟨p.val-16384,by omega⟩
    let r := BinaryBlockWrite.row w b
    ⟨r.write,r.move,pack src (if w.val % 16 = 14 then ready else write r.next),false⟩
  else if h : p.val < 147482 then
    if p.val ≤ 147457 then ⟨b,.left,pack src ready,false⟩
    else ⟨b,.left,pack src ⟨p.val-1,by have hp := p.isLt; dsimp [L] at hp; omega⟩,false⟩
  else ⟨b,.right,pack src ready,false⟩

def machine {m : Nat} (tab : SourceTable m) (start : Fin m) : Machine (Total m) where
  table := ⟨Vector.ofFn fun q => (row tab q false,row tab q true)⟩
  start := pack start ready
  blank := false
  startHead := 0

def scanConfig {m : Nat} (q : Fin m) (c : Config 16384) : Config (Total m) :=
  ⟨pack q (scan c.state),c.head,c.tape⟩

def begin {m : Nat} (q : Fin m) (tape : Int → Bool) (head : Int) : Config (Total m) :=
  scanConfig q (BinaryBlockScan.begin tape head)

theorem table_row {m : Nat} (tab : SourceTable m) (start : Fin m) (q : Fin (Total m)) (b : Bool) :
    (machine tab start).table.row q b = row tab q b := by
  cases b <;> simp [machine,Table.row]

theorem scan_row {m : Nat} (tab : SourceTable m) (q : Fin m) (s : Fin 16384) (b : Bool)
    (h : s.val < 8192) :
    row tab (pack q (scan s)) b = ⟨b,.right,pack q (scan (BinaryBlockScan.next s b)),false⟩ := by
  simp [row,source_pack,slot_pack,scan,h]

theorem scan_step {m : Nat} (tab : SourceTable m) (start q : Fin m) (c : Config 16384)
    (h : c.state.val < 8192) :
    (machine tab start).step (scanConfig q c) = (scanConfig q (BinaryBlockScan.scanner.step c).1,false) := by
  rw [BinaryBlockScan.step]
  simp only [Prod.fst]
  unfold Machine.step
  simp only [scanConfig]
  rw [table_row,scan_row tab q c.state (c.tape c.head) h]
  simp [scanConfig,Move.apply]
  funext i
  by_cases hi : i = c.head <;> simp [Config.write,hi]

theorem scan_run {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Bool) (head : Int) (k : Nat) (hk : k ≤ 13) :
    (machine tab start).system.advance (begin q tape head) k =
      scanConfig q (BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin tape head) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : k ≤ 13 := by omega
    have hs := (BinaryBlockScan.scan tape head k hp).1
    have hl := BinaryBlockScan.index_live tape head k (by omega)
    change ((machine tab start).step ((machine tab start).system.advance (begin q tape head) k)).1 = _
    rw [ih hp,scan_step tab start q _ (by simpa [hs] using hl)]
    rfl

/-- A scanner leaf is the 13-bit word used as the finite source-table index. -/
def leafIndex (s : Fin 16384) (h : 8192 ≤ s.val) : Fin 8192 :=
  ⟨s.val-8192,by have := s.isLt; omega⟩

theorem scan_path (tape : Int → Alphabet) (position : Int) :
    (BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13).state.val =
      BinaryBlockScan.path (encode (tape position)) := by
  have hs := (BinaryBlockScan.scan (binaryTape tape) (13*position) 13 (by decide)).1
  rw [hs,BinaryBlockScan.index_path]
  change BinaryBlockScan.path (readBlock (binaryTape tape) position) = _
  rw [readBlock_binaryTape]

set_option maxRecDepth 16384 in
theorem scan_leaf_index (tape : Int → Alphabet) (position : Int) :
    let s := (BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13).state
    leafIndex s (BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)) =
      BinaryBlockWrite.wordOf (tape position) := by
  apply Fin.ext
  change (BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13).state.val - 8192 =
    BinaryBlockScan.path (encode (tape position)) - 8192
  rw [scan_path]

def selected {m : Nat} (tab : SourceTable m) (q : Fin m) (a : Alphabet) : SourceRow m :=
  (tab.get q).get (BinaryBlockWrite.wordOf a)

theorem leaf_row {m : Nat} (tab : SourceTable m) (q : Fin m) (s : Fin 16384)
    (h : 8192 ≤ s.val) (b : Bool) :
    row tab (pack q (scan s)) b =
      let r := (tab.get q).get (leafIndex s h)
      match r.action with
      | .write a => ⟨b,.left,pack r.next (write (BinaryBlockWrite.state (BinaryBlockWrite.wordOf a) ⟨1,by decide⟩)),r.beep⟩
      | .left => ⟨b,.left,pack r.next (left ⟨25,by decide⟩),r.beep⟩
      | .right => ⟨b,.left,pack r.next right,r.beep⟩ := by
  have h1 : ¬(scan s).val < 8192 := by change ¬s.val < 8192; omega
  have h2 : (scan s).val < 16384 := s.isLt
  simp only [row,source_pack,slot_pack,dif_neg h1,dif_pos h2]
  rfl

/-- A correct scan selects the fixed source row for its encoded input word;
its event bit is emitted on the dispatch transition. -/
theorem dispatch_event {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int) :
    (machine tab start).system.BeepFrom (begin q (binaryTape tape) (13*position)) 13 ↔
      (selected tab q (tape position)).beep = true := by
  let c := BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13
  have hl : 8192 ≤ c.state.val := BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)
  have hi : leafIndex c.state hl = BinaryBlockWrite.wordOf (tape position) := scan_leaf_index tape position
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 13)).2 = true ↔ _
  rw [scan_run tab start q (binaryTape tape) (13*position) 13 (by decide)]
  unfold Machine.step
  simp only [scanConfig]
  rw [table_row,leaf_row tab q c.state hl (c.tape c.head),hi]
  unfold selected
  cases hact : ((tab.get q).get (BinaryBlockWrite.wordOf (tape position))).action <;> simp [hact]

def dispatchSlot : Action → Fin L
  | .write a => write (BinaryBlockWrite.state (BinaryBlockWrite.wordOf a) ⟨1,by decide⟩)
  | .left => left ⟨25,by decide⟩
  | .right => right

/-- After exactly 13 silent scan transitions, the next transition carries
the selected row's destination source state into the chosen operation path. -/
theorem dispatch_transition {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int) :
    let r := selected tab q (tape position)
    (machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 13) =
      (⟨pack r.next (dispatchSlot r.action),13*position+12,binaryTape tape⟩,r.beep) := by
  let c := BinaryBlockScan.scanner.system.advance (BinaryBlockScan.begin (binaryTape tape) (13*position)) 13
  have hl : 8192 ≤ c.state.val := BinaryBlockScan.scan_leaf (binaryTape tape) (13*position)
  have hi : leafIndex c.state hl = BinaryBlockWrite.wordOf (tape position) := scan_leaf_index tape position
  have ⟨_,hh,ht⟩ := BinaryBlockScan.scan_block tape position
  rw [scan_run tab start q (binaryTape tape) (13*position) 13 (by decide)]
  unfold Machine.step
  simp only [scanConfig]
  rw [table_row,leaf_row tab q c.state hl (c.tape c.head),hi]
  unfold selected
  have hwrite : ∀ d : Config (Total m), d.write (d.tape d.head) = d.tape := by
    intro d
    funext i
    by_cases h : i = d.head <;> simp [Config.write,h]
  cases hact : ((tab.get q).get (BinaryBlockWrite.wordOf (tape position))).action <;>
    simp [dispatchSlot,hact,Move.apply,hwrite,c,hh,ht] <;> try omega

theorem before_dispatch_silent {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Bool) (head : Int) (k : Nat) (hk : k < 13) :
    ¬ (machine tab start).system.BeepFrom (begin q tape head) k := by
  have hs := (BinaryBlockScan.scan tape head k (by omega)).1
  have hl := BinaryBlockScan.index_live tape head k hk
  change ((machine tab start).step ((machine tab start).system.advance (begin q tape head) k)).2 ≠ true
  rw [scan_run tab start q tape head k (by omega),scan_step tab start q _ (by simpa [hs] using hl)]
  simp

def writerConfig {m : Nat} (q : Fin m) (c : Config 131072) : Config (Total m) :=
  ⟨pack q (write c.state),c.head,c.tape⟩

theorem writer_row_live {m : Nat} (tab : SourceTable m) (q : Fin m) (s : Fin 131072) (b : Bool)
    (hphase : s.val % 16 ≠ 14) :
    row tab (pack q (write s)) b =
      let r := BinaryBlockWrite.row s b
      ⟨r.write,r.move,pack q (write r.next),false⟩ := by
  have h1 : ¬(write s).val < 8192 := by change ¬16384+s.val < 8192; omega
  have h2 : ¬(write s).val < 16384 := by change ¬16384+s.val < 16384; omega
  have h3 : (write s).val < 147456 := by change 16384+s.val < 147456; have := s.isLt; omega
  change row tab (pack q (write s)) b = _
  simp only [row,source_pack,slot_pack,dif_neg h1,dif_neg h2,dif_pos h3]
  have he : (⟨(write s).val-16384,by have := (write s).isLt; dsimp [L] at *; omega⟩ : Fin 131072) = s := by
    apply Fin.ext
    change 16384+s.val-16384=s.val
    omega
  rw [he]
  have hv : (write s).val-16384 = s.val := by change 16384+s.val-16384=s.val; omega
  rw [hv,if_neg hphase]

theorem writer_step_live {m : Nat} (tab : SourceTable m) (start q : Fin m) (c : Config 131072)
    (hphase : c.state.val % 16 ≠ 14) :
    (machine tab start).step (writerConfig q c) = (writerConfig q (BinaryBlockWrite.writer.step c).1,false) := by
  rw [BinaryBlockWrite.step]
  simp only [Prod.fst]
  unfold Machine.step
  simp only [writerConfig]
  rw [table_row,writer_row_live tab q c.state (c.tape c.head) hphase]
  simp only [writerConfig,Prod.mk.injEq]
  constructor
  · rfl
  · trivial

/-- The first 13 writer-phase transitions preserve the destination source
state while applying the previously verified writer table. -/
theorem writer_run_live {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (word : BinaryBlockWrite.Word) (tape : Int → Bool) (head : Int) (k : Nat) (hk : k ≤ 13) :
    (machine tab start).system.advance
      (writerConfig q (BinaryBlockWrite.writer.system.advance (BinaryBlockWrite.begin word tape head) 1)) k =
    writerConfig q (BinaryBlockWrite.writer.system.advance (BinaryBlockWrite.begin word tape head) (1+k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : k ≤ 13 := by omega
    have hw := BinaryBlockWrite.write_run word tape head k hp
    have hphase : ((BinaryBlockWrite.writer.system.advance (BinaryBlockWrite.begin word tape head) (1+k)).state.val % 16) ≠ 14 := by
      rw [hw,BinaryBlockWrite.state_phase]
      simp
      omega
    change ((machine tab start).step ((machine tab start).system.advance _ k)).1 = _
    rw [ih hp,writer_step_live tab start q _ hphase]
    rfl

theorem writer_row_final {m : Nat} (tab : SourceTable m) (q : Fin m)
    (word : BinaryBlockWrite.Word) (b : Bool) :
    row tab (pack q (write (BinaryBlockWrite.state word ⟨14,by decide⟩))) b =
      ⟨b,.right,pack q ready,false⟩ := by
  let s := BinaryBlockWrite.state word ⟨14,by decide⟩
  have h1 : ¬(write s).val < 8192 := by change ¬16384+s.val < 8192; omega
  have h2 : ¬(write s).val < 16384 := by change ¬16384+s.val < 16384; omega
  have h3 : (write s).val < 147456 := by change 16384+s.val < 147456; have := s.isLt; omega
  change row tab (pack q (write s)) b = _
  simp only [row,source_pack,slot_pack,dif_neg h1,dif_neg h2,dif_pos h3]
  have he : (⟨(write s).val-16384,by have := (write s).isLt; dsimp [L] at *; omega⟩ : Fin 131072) = s := by
    apply Fin.ext
    change 16384+s.val-16384=s.val
    omega
  have hv : (write s).val-16384 = s.val := by change 16384+s.val-16384=s.val; omega
  rw [he,hv]
  simp [s,BinaryBlockWrite.row,BinaryBlockWrite.state_phase]

theorem writer_final_step {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (word : BinaryBlockWrite.Word) (tape : Int → Bool) (head : Int) :
    (machine tab start).step (writerConfig q ⟨BinaryBlockWrite.state word ⟨14,by decide⟩,head,tape⟩) =
      (⟨pack q ready,head+1,tape⟩,false) := by
  unfold Machine.step
  simp only [writerConfig]
  rw [table_row,writer_row_final]
  simp [Move.apply]
  funext i
  by_cases hi : i = head <;> simp [Config.write,hi]

/-- A source write row completes in 28 concrete transitions, returning
straight to the destination source state's scanner. -/
theorem complete_write {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int) (a : Alphabet)
    (hact : (selected tab q (tape position)).action = .write a) :
    (machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 28 =
      ⟨pack (selected tab q (tape position)).next ready,13*position,
        binaryTape (Function.update tape position a)⟩ := by
  let r := selected tab q (tape position)
  let w := BinaryBlockWrite.wordOf a
  have h14 : (machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 14 =
      writerConfig r.next (BinaryBlockWrite.writer.system.advance
        (BinaryBlockWrite.begin w (binaryTape tape) (13*position+13)) 1) := by
    change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 13)).1 = _
    rw [dispatch_transition tab start q tape position,BinaryBlockWrite.first]
    simp [r,w,hact,dispatchSlot,writerConfig]
    omega
  rw [show 28 = 14+13+1 by decide,EventSystem.advance,BinaryReadWrite.advance_add,h14,
    writer_run_live tab start r.next w (binaryTape tape) (13*position+13) 13 (by decide),
    BinaryBlockWrite.write_run w (binaryTape tape) (13*position+13) 13 (by decide)]
  change ((machine tab start).step (writerConfig r.next
    ⟨BinaryBlockWrite.state w ⟨14,by decide⟩,13*position+13-14,
      BinaryBlockWrite.written w (binaryTape tape) (13*position+13) 13⟩)).1 = _
  rw [writer_final_step]
  simp [r,w,BinaryBlockWrite.written_binary_update]
  congr 1 <;> omega

theorem dispatch_write {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int) (a : Alphabet)
    (hact : (selected tab q (tape position)).action = .write a) :
    (machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 14 =
      writerConfig (selected tab q (tape position)).next
        (BinaryBlockWrite.writer.system.advance
          (BinaryBlockWrite.begin (BinaryBlockWrite.wordOf a) (binaryTape tape) (13*position+13)) 1) := by
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 13)).1 = _
  rw [dispatch_transition tab start q tape position,BinaryBlockWrite.first]
  simp [hact,dispatchSlot,writerConfig]
  omega

theorem write_phase_silent {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int) (a : Alphabet)
    (hact : (selected tab q (tape position)).action = .write a) (k : Nat) (hk : k < 13) :
    ¬ (machine tab start).system.BeepFrom (begin q (binaryTape tape) (13*position)) (14+k) := by
  let w := BinaryBlockWrite.wordOf a
  let b := BinaryBlockWrite.begin w (binaryTape tape) (13*position+13)
  have hw := BinaryBlockWrite.write_run w (binaryTape tape) (13*position+13) k (by omega)
  have hp : (BinaryBlockWrite.writer.system.advance b (1+k)).state.val % 16 ≠ 14 := by
    rw [hw,BinaryBlockWrite.state_phase]
    simp
    omega
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) (14+k))).2 ≠ true
  rw [BinaryReadWrite.advance_add,dispatch_write tab start q tape position a hact,
    writer_run_live tab start (selected tab q (tape position)).next w (binaryTape tape) (13*position+13) k (by omega),
    writer_step_live tab start _ _ hp]
  simp

theorem write_final_silent {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int) (a : Alphabet)
    (hact : (selected tab q (tape position)).action = .write a) :
    ¬ (machine tab start).system.BeepFrom (begin q (binaryTape tape) (13*position)) 27 := by
  let w := BinaryBlockWrite.wordOf a
  change ((machine tab start).step ((machine tab start).system.advance (begin q (binaryTape tape) (13*position)) 27)).2 ≠ true
  rw [show 27 = 14+13 by decide,BinaryReadWrite.advance_add,dispatch_write tab start q tape position a hact,
    writer_run_live tab start (selected tab q (tape position)).next w (binaryTape tape) (13*position+13) 13 (by decide),
    BinaryBlockWrite.write_run w (binaryTape tape) (13*position+13) 13 (by decide),writer_final_step]
  simp

/-- The 28-transition write segment contains exactly the source row's event. -/
theorem write_trace {m : Nat} (tab : SourceTable m) (start q : Fin m)
    (tape : Int → Alphabet) (position : Int) (a : Alphabet)
    (hact : (selected tab q (tape position)).action = .write a) (k : Nat) (hk : k < 28) :
    (machine tab start).system.BeepFrom (begin q (binaryTape tape) (13*position)) k ↔
      k = 13 ∧ (selected tab q (tape position)).beep = true := by
  constructor
  · intro h
    by_cases hpre : k < 13
    · exact False.elim (before_dispatch_silent tab start q (binaryTape tape) (13*position) k hpre h)
    · by_cases hd : k = 13
      · exact ⟨hd,(dispatch_event tab start q tape position).1 (hd ▸ h)⟩
      · by_cases hmid : k < 27
        · have he : k = 14+(k-14) := by omega
          rw [he] at h
          exact False.elim (write_phase_silent tab start q tape position a hact (k-14) (by omega) h)
        · have he : k = 27 := by omega
          subst k
          exact False.elim (write_final_silent tab start q tape position a hact h)
  · rintro ⟨rfl,h⟩
    exact (dispatch_event tab start q tape position).2 h

end Shared.Beeping.BinarySourceCompiler
