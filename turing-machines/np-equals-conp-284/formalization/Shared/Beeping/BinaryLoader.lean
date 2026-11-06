import Shared.Beeping.BinarySourceLoaded

/-! A finite silent bootstrap for a fixed bit payload. It writes the payload
on a blank tape, returns to the initial head position, and enters a supplied
binary table. The table and payload are parameters, not implicit inputs. -/
namespace Shared.Beeping.BinaryLoader
open Shared.Beeping.Machines

def payload (blank : Bool) (bits : List Bool) : List Bool :=
  if bits = [] then [blank] else bits

theorem payload_pos (blank : Bool) (bits : List Bool) : 0 < (payload blank bits).length := by
  cases bits <;> simp [payload]

def count (blank : Bool) (bits : List Bool) : Nat := (payload blank bits).length

theorem count_eq_max (blank : Bool) (bits : List Bool) : count blank bits = max bits.length 1 := by
  cases bits <;> simp [count,payload]

def total {n : Nat} (M : Machine n) (bits : List Bool) : Nat := 2 * count M.blank bits + n

def liftState {n : Nat} (M : Machine n) (bits : List Bool) (q : Fin n) : Fin (total M bits) :=
  ⟨2*count M.blank bits+q.val,by have := q.isLt; dsimp [total]; omega⟩

def embed {n : Nat} (M : Machine n) (bits : List Bool) (c : Config n) : Config (total M bits) :=
  ⟨liftState M bits c.state,c.head,c.tape⟩

def row {n : Nat} (M : Machine n) (bits : List Bool) (q : Fin (total M bits)) (read : Bool) : Row (total M bits) :=
  let k := count M.blank bits
  if hw : q.val < k then
    ⟨((payload M.blank bits)[q.val]?).getD M.blank,.right,
      ⟨q.val+1,by have hp : 0 < count M.blank bits := payload_pos M.blank bits; have hn := M.start.isLt; change q.val+1 < 2*count M.blank bits+n; omega⟩,false⟩
  else if hr : q.val < 2*k then
    ⟨read,.left,if q.val+1 = 2*k then liftState M bits M.start
      else ⟨q.val+1,by have hn := M.start.isLt; change q.val+1 < 2*count M.blank bits+n; omega⟩,false⟩
  else
    let s : Fin n := ⟨q.val-2*k,by have h := q.isLt; dsimp [total] at h; omega⟩
    let r := M.table.row s read
    ⟨r.write,r.move,liftState M bits r.next,r.beep⟩

def machine {n : Nat} (M : Machine n) (bits : List Bool) : Machine (total M bits) where
  table := ⟨Vector.ofFn fun q => (row M bits q false,row M bits q true)⟩
  start := ⟨0,by have h := payload_pos M.blank bits; dsimp [total,count] at *; omega⟩
  blank := M.blank
  startHead := M.startHead

theorem table_row {n : Nat} (M : Machine n) (bits : List Bool) (q : Fin (total M bits)) (b : Bool) :
    (machine M bits).table.row q b = row M bits q b := by
  cases b <;> simp [machine,Table.row]

/-- The target table's original rows are embedded without changing flags. -/
theorem target_row {n : Nat} (M : Machine n) (bits : List Bool) (q : Fin n) (b : Bool) :
    row M bits (liftState M bits q) b =
      let r := M.table.row q b
      ⟨r.write,r.move,liftState M bits r.next,r.beep⟩ := by
  have h1 : ¬(liftState M bits q).val < count M.blank bits := by
    change ¬2*count M.blank bits+q.val < count M.blank bits; omega
  have h2 : ¬(liftState M bits q).val < 2*count M.blank bits := by
    change ¬2*count M.blank bits+q.val < 2*count M.blank bits; omega
  simp only [row,dif_neg h1,dif_neg h2]
  have he : (⟨(liftState M bits q).val-2*count M.blank bits,by
      have h := (liftState M bits q).isLt; dsimp [total] at h; omega⟩ : Fin n) = q := by
    apply Fin.ext
    change 2*count M.blank bits+q.val-2*count M.blank bits=q.val
    omega
  rw [he]

theorem target_step {n : Nat} (M : Machine n) (bits : List Bool) (c : Config n) :
    (machine M bits).step (embed M bits c) = (embed M bits (M.step c).1,(M.step c).2) := by
  unfold Machine.step
  simp only [embed]
  rw [table_row,target_row]
  simp only [Prod.mk.injEq]
  constructor
  · rfl
  · trivial

theorem target_advance {n : Nat} (M : Machine n) (bits : List Bool) (c : Config n) (k : Nat) :
    (machine M bits).system.advance (embed M bits c) k = embed M bits (M.system.advance c k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((machine M bits).step ((machine M bits).system.advance (embed M bits c) k)).1 = _
    rw [ih,target_step]
    rfl

theorem target_event {n : Nat} (M : Machine n) (bits : List Bool) (c : Config n) (k : Nat) :
    (machine M bits).system.BeepFrom (embed M bits c) k ↔ M.system.BeepFrom c k := by
  change ((machine M bits).step ((machine M bits).system.advance (embed M bits c) k)).2 = true ↔ _
  rw [target_advance,target_step]
  rfl

def bootState {n : Nat} (M : Machine n) (bits : List Bool) (i : Nat)
    (h : i < 2*count M.blank bits) : Fin (total M bits) :=
  ⟨i,by have hn := M.start.isLt; dsimp [total]; omega⟩

def tapeAfter {n : Nat} (M : Machine n) (bits : List Bool) : Nat → Int → Bool
  | 0 => fun _ => M.blank
  | i+1 => Function.update (tapeAfter M bits i) (M.startHead+i)
      (((payload M.blank bits)[i]?).getD M.blank)

def loaded {n : Nat} (M : Machine n) (bits : List Bool) : Config n :=
  ⟨M.start,M.startHead,tapeAfter M bits (count M.blank bits)⟩

theorem writing_row {n : Nat} (M : Machine n) (bits : List Bool) (i : Nat)
    (hi : i < count M.blank bits) (b : Bool) :
    row M bits (bootState M bits i (by omega)) b =
      ⟨((payload M.blank bits)[i]?).getD M.blank,.right,bootState M bits (i+1) (by omega),false⟩ := by
  simp [row,bootState,hi]

theorem writing_step {n : Nat} (M : Machine n) (bits : List Bool) (i : Nat)
    (hi : i < count M.blank bits) (tape : Int → Bool) (head : Int) :
    (machine M bits).step ⟨bootState M bits i (by omega),head,tape⟩ =
      (⟨bootState M bits (i+1) (by omega),head+1,
        Function.update tape head (((payload M.blank bits)[i]?).getD M.blank)⟩,false) := by
  unfold Machine.step
  rw [table_row,writing_row M bits i hi]
  simp [Move.apply]
  funext j
  by_cases hj : j = head <;> simp [Config.write,Function.update,hj]

/-- After `i` startup transitions exactly the first `i` payload cells have
been written, and no target table row has run. -/
theorem writes {n : Nat} (M : Machine n) (bits : List Bool) (i : Nat)
    (hi : i ≤ count M.blank bits) :
    (machine M bits).system.advance (machine M bits).initial i =
      ⟨bootState M bits i (by have := payload_pos M.blank bits; dsimp [count] at *; omega),
        M.startHead+i,tapeAfter M bits i⟩ := by
  induction i with
  | zero =>
    simp [EventSystem.advance,Machine.initial,machine,bootState,tapeAfter]
  | succ i ih =>
    have hlt : i < count M.blank bits := by omega
    change ((machine M bits).step ((machine M bits).system.advance (machine M bits).initial i)).1 = _
    rw [ih (by omega),writing_step M bits i hlt]
    simp [tapeAfter,Nat.cast_add,Nat.cast_one,add_assoc]

theorem return_row {n : Nat} (M : Machine n) (bits : List Bool) (i : Nat)
    (hlo : count M.blank bits ≤ i) (hhi : i+1 < 2*count M.blank bits) (b : Bool) :
    row M bits (bootState M bits i (by omega)) b =
      ⟨b,.left,bootState M bits (i+1) (by omega),false⟩ := by
  have h1 : ¬i < count M.blank bits := by omega
  have h2 : i < 2*count M.blank bits := by omega
  have h3 : ¬i+1 = 2*count M.blank bits := by omega
  simp [row,bootState,h1,h2,h3]

theorem return_step {n : Nat} (M : Machine n) (bits : List Bool) (i : Nat)
    (hlo : count M.blank bits ≤ i) (hhi : i+1 < 2*count M.blank bits)
    (tape : Int → Bool) (head : Int) :
    (machine M bits).step ⟨bootState M bits i (by omega),head,tape⟩ =
      (⟨bootState M bits (i+1) (by omega),head-1,tape⟩,false) := by
  unfold Machine.step
  rw [table_row,return_row M bits i hlo hhi]
  simp [Move.apply]
  funext j
  by_cases hj : j = head <;> simp [Config.write,hj]

theorem final_row {n : Nat} (M : Machine n) (bits : List Bool) (b : Bool) :
    row M bits (bootState M bits (2*count M.blank bits-1)
      (by have := payload_pos M.blank bits; dsimp [count] at *; omega)) b =
      ⟨b,.left,liftState M bits M.start,false⟩ := by
  have hp : 0 < count M.blank bits := payload_pos M.blank bits
  have h1 : ¬2*count M.blank bits-1 < count M.blank bits := by omega
  have h2 : 2*count M.blank bits-1 < 2*count M.blank bits := by omega
  have h3 : 2*count M.blank bits-1+1 = 2*count M.blank bits := by omega
  simp [row,bootState,h1,h2,h3]

theorem final_step {n : Nat} (M : Machine n) (bits : List Bool) (tape : Int → Bool) (head : Int) :
    (machine M bits).step ⟨bootState M bits (2*count M.blank bits-1)
      (by have := payload_pos M.blank bits; dsimp [count] at *; omega),head,tape⟩ =
      (embed M bits ⟨M.start,head-1,tape⟩,false) := by
  unfold Machine.step
  rw [table_row,final_row]
  simp [embed,Move.apply]
  funext j
  by_cases hj : j = head <;> simp [Config.write,hj]

theorem return_prefix {n : Nat} (M : Machine n) (bits : List Bool) (j : Nat)
    (hj : j < count M.blank bits) :
    (machine M bits).system.advance (machine M bits).initial (count M.blank bits+j) =
      ⟨bootState M bits (count M.blank bits+j) (by omega),
        M.startHead+count M.blank bits-j,tapeAfter M bits (count M.blank bits)⟩ := by
  induction j with
  | zero => simpa using writes M bits (count M.blank bits) (by omega)
  | succ j ih =>
    have hj' : j < count M.blank bits := by omega
    have hlast : count M.blank bits+j+1 < 2*count M.blank bits := by omega
    change ((machine M bits).step ((machine M bits).system.advance (machine M bits).initial (count M.blank bits+j))).1 = _
    rw [ih hj']
    change ((machine M bits).step ⟨bootState M bits (count M.blank bits+j) (by omega),
      M.startHead+count M.blank bits-j,tapeAfter M bits (count M.blank bits)⟩).1 = _
    rw [return_step M bits (count M.blank bits+j) (by omega) hlast]
    simp only [Prod.fst]
    congr 1 <;> simp <;> omega

/-- Exactly `2 * count` silent startup transitions end at the target's start
state and original head position, with the payload written on the tape. -/
theorem boot_run {n : Nat} (M : Machine n) (bits : List Bool) :
    (machine M bits).system.advance (machine M bits).initial (2*count M.blank bits) =
      embed M bits (loaded M bits) := by
  have hp : 0 < count M.blank bits := payload_pos M.blank bits
  have hj : count M.blank bits-1 < count M.blank bits := by omega
  have he : 2*count M.blank bits = (count M.blank bits+(count M.blank bits-1))+1 := by omega
  rw [he,EventSystem.advance,return_prefix M bits _ hj]
  have hs : count M.blank bits+(count M.blank bits-1) = 2*count M.blank bits-1 := by omega
  have hstate : bootState M bits (count M.blank bits+(count M.blank bits-1)) (by omega) =
      bootState M bits (2*count M.blank bits-1) (by omega) := by
    apply Fin.ext
    simp [bootState,hs]
  rw [hstate]
  change ((machine M bits).step _).1 = _
  rw [final_step]
  simp [loaded,embed]
  congr 1 <;> omega

theorem payload_getD (blank : Bool) (bits : List Bool) (i : Nat) :
    ((payload blank bits)[i]?).getD blank = (bits[i]?).getD blank := by
  cases bits with
  | nil => cases i <;> simp [payload]
  | cons b bs => simp [payload]

theorem bits_length_le_count (blank : Bool) (bits : List Bool) : bits.length ≤ count blank bits := by
  cases bits <;> simp [count,payload]

theorem tapeAfter_at {n : Nat} (M : Machine n) (bits : List Bool) (i j : Nat) :
    tapeAfter M bits i (M.startHead+j) =
      if j < i then ((payload M.blank bits)[j]?).getD M.blank else M.blank := by
  induction i with
  | zero => simp [tapeAfter]
  | succ i ih =>
    by_cases he : j = i
    · subst j
      simp [tapeAfter]
    · have hn : M.startHead+(j : Int) ≠ M.startHead+(i : Int) := by omega
      simp only [tapeAfter,Function.update_of_ne hn,ih]
      by_cases hj : j < i <;> simp [hj] <;> omega

/-- Every nonnegative offset reads exactly the requested payload, with blank
padding; the empty payload leaves the initially blank tape unchanged. -/
theorem loaded_at {n : Nat} (M : Machine n) (bits : List Bool) (j : Nat) :
    (loaded M bits).tape (M.startHead+j) = (bits[j]?).getD M.blank := by
  change tapeAfter M bits (count M.blank bits) (M.startHead+j) = _
  rw [tapeAfter_at]
  by_cases hj : j < count M.blank bits
  · simp [hj,payload_getD]
  · have hn : bits[j]? = none := List.getElem?_eq_none (by have := bits_length_le_count M.blank bits; omega)
    simp [hj,hn]

theorem tapeAfter_outside {n : Nat} (M : Machine n) (bits : List Bool) (k : Nat) (i : Int)
    (h : i < M.startHead ∨ M.startHead+k ≤ i) : tapeAfter M bits k i = M.blank := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hn : i ≠ M.startHead+(k : Int) := by omega
    simp only [tapeAfter,Function.update_of_ne hn]
    exact ih (by omega)

theorem loaded_empty {n : Nat} (M : Machine n) : (loaded M []).tape = fun _ => M.blank := by
  funext i
  by_cases hi : i = M.startHead <;>
    simp [loaded,count,payload,tapeAfter,Function.update,hi]

/-- Positions outside the fixed payload remain blank. -/
theorem loaded_outside {n : Nat} (M : Machine n) (bits : List Bool) (i : Int)
    (h : i < M.startHead ∨ M.startHead+bits.length ≤ i) : (loaded M bits).tape i = M.blank := by
  cases bits with
  | nil => rw [loaded_empty]
  | cons b bs =>
    change tapeAfter M (b::bs) (count M.blank (b::bs)) i = _
    apply tapeAfter_outside
    simpa [count,payload] using h

theorem boot_row_silent {n : Nat} (M : Machine n) (bits : List Bool) (q : Fin (total M bits))
    (b : Bool) (h : q.val < 2*count M.blank bits) : (row M bits q b).beep = false := by
  by_cases hq : q.val < count M.blank bits
  · simp [row,hq]
  · simp [row,hq,h]

theorem run_eq_advance {α : Type} (S : EventSystem α) (k : Nat) : S.run k = S.advance S.initial k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [EventSystem.run_succ,EventSystem.advance,ih]

theorem boot_silent {n : Nat} (M : Machine n) (bits : List Bool) (t : Nat)
    (ht : t < 2*count M.blank bits) : ¬ (machine M bits).system.BeepAt t := by
  rw [EventSystem.BeepAt,run_eq_advance]
  change ¬ ((machine M bits).step ((machine M bits).system.advance (machine M bits).initial t)).2 = true
  by_cases h : t < count M.blank bits
  · rw [writes M bits t (by omega)]
    change ((machine M bits).table.row _ _).beep ≠ true
    rw [table_row,boot_row_silent M bits _ _ (by change t < _; omega)]
    decide
  · have hj : t-count M.blank bits < count M.blank bits := by omega
    have he : t = count M.blank bits+(t-count M.blank bits) := by omega
    rw [he,return_prefix M bits _ hj]
    change ((machine M bits).table.row _ _).beep ≠ true
    rw [table_row,boot_row_silent M bits _ _ (by change count M.blank bits+(t-count M.blank bits) < _; omega)]
    decide

def loadedSystem {n : Nat} (M : Machine n) (bits : List Bool) : EventSystem (Config n) :=
  ⟨loaded M bits,M.step⟩

theorem loaded_run {n : Nat} (M : Machine n) (bits : List Bool) (k : Nat) :
    (loadedSystem M bits).run k = M.system.advance (loaded M bits) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (M.step ((loadedSystem M bits).run k)).1 = (M.step (M.system.advance (loaded M bits) k)).1
    rw [ih]

theorem event_shift {n : Nat} (M : Machine n) (bits : List Bool) (k : Nat) :
    (machine M bits).system.BeepAt (2*count M.blank bits+k) ↔ (loadedSystem M bits).BeepAt k := by
  rw [EventSystem.beepAt_add_iff,run_eq_advance]
  change (machine M bits).system.BeepFrom ((machine M bits).system.advance (machine M bits).initial (2*count M.blank bits)) k ↔ _
  rw [boot_run,target_event]
  change M.system.BeepFrom (loaded M bits) k ↔ (M.step ((loadedSystem M bits).run k)).2 = true
  rw [loaded_run]
  rfl

theorem eventuallySilent_iff {n : Nat} (M : Machine n) (bits : List Bool) :
    (machine M bits).system.EventuallySilent ↔ (loadedSystem M bits).EventuallySilent := by
  rw [EventSystem.eventuallySilent_iff_shift (machine M bits).system (2*count M.blank bits)]
  simp only [event_shift]
  rfl

theorem infinitelyManyBeeps_iff {n : Nat} (M : Machine n) (bits : List Bool) :
    (machine M bits).system.InfinitelyManyBeeps ↔ (loadedSystem M bits).InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    ← EventSystem.not_eventuallySilent_iff_infinitelyMany]
  exact not_congr (eventuallySilent_iff M bits)

/-- A concrete fixed payload that establishes the stated tape equality gives
an actual blank-start compiler theorem. The equality remains a binding
obligation for a later source program and its initial data. -/
theorem compiled_eventuallySilent_iff {m : Nat} (tab : BinarySourceCompiler.SourceTable m)
    (start : Fin m) (initial : BinarySourceRefinement.SourceConfig m) (bits : List Bool)
    (h : loaded (BinarySourceCompiler.machine tab start) bits =
      BinarySourceCompiler.begin initial.state (ComparisonAlphabetBits.binaryTape initial.tape) (13*initial.head)) :
    (machine (BinarySourceCompiler.machine tab start) bits).system.EventuallySilent ↔
      (BinarySourceLoaded.sourceFrom tab initial).EventuallySilent := by
  have he : loadedSystem (BinarySourceCompiler.machine tab start) bits =
      BinarySourceLoaded.binaryFrom tab start initial := by
    change EventSystem.mk (loaded (BinarySourceCompiler.machine tab start) bits)
      (BinarySourceCompiler.machine tab start).step =
      EventSystem.mk (BinarySourceCompiler.begin initial.state (ComparisonAlphabetBits.binaryTape initial.tape) (13*initial.head))
        (BinarySourceCompiler.machine tab start).step
    rw [h]
  rw [eventuallySilent_iff,he]
  exact BinarySourceLoaded.eventuallySilent_iff tab start initial

namespace Fixtures
example (blank : Bool) : count blank [] = 1 := by cases blank <;> decide
example {n : Nat} (M : Machine n) : (loaded M []).tape = fun _ => M.blank := loaded_empty M
example {n : Nat} (M : Machine n) : (loaded M [true,false]).tape M.startHead = true := by
  simpa using loaded_at M [true,false] 0
example {n : Nat} (M : Machine n) : (loaded M [true,false]).tape (M.startHead+1) = false := by
  simpa using loaded_at M [true,false] 1
end Fixtures

end Shared.Beeping.BinaryLoader
