import Shared.Beeping.Events

/-!
A finite, total binary machine with transition flags. States are `Fin n`;
for each state the vector stores both fixed transition rows. A beep is the
flag of the row actually taken, never a predicate on the tape or on time.
The integer-indexed tape is initially constant blank. Time `t` labels the
transition out of configuration `t`.

This module defines the semantic interface. Byte serialization and later
binding obligations are supplied by TableBits and MachineBindings.
-/
namespace Shared.Beeping.Machines

inductive Move where
  | left | right
  deriving DecidableEq, Repr

def Move.apply (m : Move) (position : Int) : Int :=
  match m with
  | .left => position - 1
  | .right => position + 1

structure Row (n : Nat) where
  write : Bool
  move : Move
  next : Fin n
  beep : Bool
  deriving DecidableEq, Repr

/-- Each state has the row for `false` followed by the row for `true`. -/
structure Table (n : Nat) where
  rows : Vector (Row n × Row n) n
  deriving Repr

def Table.row {n : Nat} (table : Table n) (q : Fin n) (read : Bool) : Row n :=
  if read then table.rows[q].2 else table.rows[q].1

structure Machine (n : Nat) where
  table : Table n
  start : Fin n
  blank : Bool
  startHead : Int

structure Config (n : Nat) where
  state : Fin n
  head : Int
  tape : Int → Bool

def Config.write {n : Nat} (c : Config n) (symbol : Bool) : Int → Bool :=
  fun pos => if pos = c.head then symbol else c.tape pos

@[simp] theorem Config.write_head {n : Nat} (c : Config n) (b : Bool) :
    c.write b c.head = b := by simp [Config.write]

theorem Config.write_other {n : Nat} (c : Config n) (b : Bool) (p : Int)
    (hp : p ≠ c.head) : c.write b p = c.tape p := by simp [Config.write, hp]

def Machine.initial {n : Nat} (M : Machine n) : Config n :=
  ⟨M.start, M.startHead, fun _ => M.blank⟩

def Machine.step {n : Nat} (M : Machine n) (c : Config n) : Config n × Bool :=
  let row := M.table.row c.state (c.tape c.head)
  (⟨row.next, row.move.apply c.head, c.write row.write⟩, row.beep)

def Machine.system {n : Nat} (M : Machine n) : EventSystem (Config n) :=
  ⟨M.initial, M.step⟩

@[simp] theorem Machine.beepAt_iff_row_flag {n : Nat} (M : Machine n) (t : Nat) :
    M.system.BeepAt t ↔
      (M.table.row (M.system.run t).state
        ((M.system.run t).tape (M.system.run t).head)).beep = true := by
  rfl

@[simp] theorem Machine.next_state {n : Nat} (M : Machine n) (t : Nat) :
    (M.system.run (t + 1)).state =
      (M.table.row (M.system.run t).state
        ((M.system.run t).tape (M.system.run t).head)).next := by
  rfl

/-- A finite mask contains exactly two flags per state. -/
abbrev Flags (n : Nat) := Vector (Bool × Bool) n

def Flags.at {n : Nat} (flags : Flags n) (q : Fin n) (read : Bool) : Bool :=
  if read then flags[q].2 else flags[q].1

def Row.withFlag {n : Nat} (row : Row n) (flag : Bool) : Row n :=
  {row with beep := flag}

def Table.withFlags {n : Nat} (table : Table n) (flags : Flags n) : Table n :=
  ⟨Vector.ofFn fun q =>
    ((table.row q false).withFlag (flags.at q false),
     (table.row q true).withFlag (flags.at q true))⟩

theorem Table.row_withFlags {n : Nat} (table : Table n) (flags : Flags n)
    (q : Fin n) (read : Bool) :
    (table.withFlags flags).row q read = (table.row q read).withFlag (flags.at q read) := by
  cases read <;> simp [Table.row, Table.withFlags, Flags.at]

def Machine.withFlags {n : Nat} (M : Machine n) (flags : Flags n) : Machine n :=
  {M with table := M.table.withFlags flags}

/-- Changing the finite event mask leaves the configurations of the run unchanged. -/
theorem Machine.step_withFlags_config {n : Nat} (M : Machine n) (flags : Flags n)
    (c : Config n) : ((M.withFlags flags).step c).1 = (M.step c).1 := by
  simp [Machine.step, Machine.withFlags, Table.row_withFlags, Row.withFlag]

theorem Machine.run_withFlags {n : Nat} (M : Machine n) (flags : Flags n) (t : Nat) :
    (M.withFlags flags).system.run t = M.system.run t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [EventSystem.run_succ, ih]
    exact Machine.step_withFlags_config M flags _

theorem Machine.beepAt_withFlags {n : Nat} (M : Machine n) (flags : Flags n) (t : Nat) :
    (M.withFlags flags).system.BeepAt t ↔
      flags.at (M.system.run t).state ((M.system.run t).tape (M.system.run t).head) = true := by
  rw [Machine.beepAt_iff_row_flag, Machine.run_withFlags]
  simp [Machine.withFlags, Table.row_withFlags, Row.withFlag]

/-- Construct a finite mask from its two flags for each finite state. -/
def Flags.ofFn {n : Nat} (f : Fin n → Bool → Bool) : Flags n :=
  Vector.ofFn fun q => (f q false, f q true)

@[simp] theorem Flags.at_ofFn {n : Nat} (f : Fin n → Bool → Bool)
    (q : Fin n) (read : Bool) : (Flags.ofFn f).at q read = f q read := by
  cases read <;> simp [Flags.ofFn, Flags.at]

/-- Mark all rows leaving one of the states in the finite mask. -/
def Flags.exitingStates {n : Nat} (states : Vector Bool n) : Flags n :=
  Flags.ofFn fun q _ => states[q]

/-- Mark all rows entering one of the states in the finite mask. -/
def Flags.enteringStates {n : Nat} (table : Table n) (states : Vector Bool n) : Flags n :=
  Flags.ofFn fun q read => states[(table.row q read).next]

/-- Historical exit-state convention, here represented by finite row flags. -/
def Flags.exiting {n : Nat} (B : Fin n) : Flags n :=
  Flags.ofFn fun q _ => decide (q = B)

/-- Entry-state convention, here represented by finite row flags. -/
def Flags.entering {n : Nat} (table : Table n) (B : Fin n) : Flags n :=
  Flags.ofFn fun q read => decide ((table.row q read).next = B)

/-- Mark exactly one input-symbol row of a state. -/
def Flags.single {n : Nat} (B : Fin n) (symbol : Bool) : Flags n :=
  Flags.ofFn fun q read => decide (q = B ∧ read = symbol)

def Machine.exitingStates {n : Nat} (M : Machine n) (states : Vector Bool n) : Machine n :=
  M.withFlags (Flags.exitingStates states)

def Machine.enteringStates {n : Nat} (M : Machine n) (states : Vector Bool n) : Machine n :=
  M.withFlags (Flags.enteringStates M.table states)

def Machine.exiting {n : Nat} (M : Machine n) (B : Fin n) : Machine n :=
  M.withFlags (Flags.exiting B)

def Machine.entering {n : Nat} (M : Machine n) (B : Fin n) : Machine n :=
  M.withFlags (Flags.entering M.table B)

def Machine.singleMarked {n : Nat} (M : Machine n) (B : Fin n) (symbol : Bool) : Machine n :=
  M.withFlags (Flags.single B symbol)

/-- Occupancy at time zero does not itself emit an event: this checks the row
exited by the first transition. -/
theorem Machine.exiting_beep_iff {n : Nat} (M : Machine n) (B : Fin n) (t : Nat) :
    (M.exiting B).system.BeepAt t ↔ (M.system.run t).state = B := by
  rw [Machine.exiting, Machine.beepAt_withFlags]
  simp [Flags.exiting]

/-- The entry convention counts the destination of the transition, not the
initial state before any transition. -/
theorem Machine.entering_beep_iff {n : Nat} (M : Machine n) (B : Fin n) (t : Nat) :
    (M.entering B).system.BeepAt t ↔ (M.system.run (t + 1)).state = B := by
  rw [Machine.entering, Machine.beepAt_withFlags, Machine.next_state]
  simp [Flags.entering]

theorem Machine.singleMarked_beep_iff {n : Nat} (M : Machine n) (B : Fin n)
    (symbol : Bool) (t : Nat) :
    (M.singleMarked B symbol).system.BeepAt t ↔
      (M.system.run t).state = B ∧
        (M.system.run t).tape (M.system.run t).head = symbol := by
  rw [Machine.singleMarked, Machine.beepAt_withFlags]
  simp [Flags.single]

theorem Machine.exitingStates_beep_iff {n : Nat} (M : Machine n)
    (states : Vector Bool n) (t : Nat) :
    (M.exitingStates states).system.BeepAt t ↔ states[(M.system.run t).state] = true := by
  rw [Machine.exitingStates, Machine.beepAt_withFlags]
  simp [Flags.exitingStates]

theorem Machine.enteringStates_beep_iff {n : Nat} (M : Machine n)
    (states : Vector Bool n) (t : Nat) :
    (M.enteringStates states).system.BeepAt t ↔ states[(M.system.run (t + 1)).state] = true := by
  rw [Machine.enteringStates, Machine.beepAt_withFlags]
  simp only [Flags.enteringStates, Flags.at_ofFn]
  have h := congrArg (fun q : Fin n => states[q]) (Machine.next_state M t)
  rw [h]

/-- If the replacement finite mask agrees on every row, the event trace is
unchanged. The implication is pointwise on finite transition-table rows. -/
theorem Machine.reflag_beep_iff {n : Nat} (M : Machine n) (flags : Flags n)
    (hflags : ∀ q read, (M.table.row q read).beep = flags.at q read) (t : Nat) :
    (M.withFlags flags).system.BeepAt t ↔ M.system.BeepAt t := by
  rw [Machine.beepAt_withFlags, Machine.beepAt_iff_row_flag, hflags]

theorem Machine.reflag_eventuallySilent_iff {n : Nat} (M : Machine n) (flags : Flags n)
    (hflags : ∀ q read, (M.table.row q read).beep = flags.at q read) :
    (M.withFlags flags).system.EventuallySilent ↔ M.system.EventuallySilent := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht hb
    exact hT t ht ((Machine.reflag_beep_iff M flags hflags t).2 hb)
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht hb
    exact hT t ht ((Machine.reflag_beep_iff M flags hflags t).1 hb)

/-- On the blank-start run, only finitely many tape positions can differ from
blank after any finite number of transitions. The list may contain duplicates
and cells that were written back to blank. -/
theorem Machine.run_finite_support {n : Nat} (M : Machine n) (t : Nat) :
    ∃ touched : List Int, ∀ pos, pos ∉ touched → (M.system.run t).tape pos = M.blank := by
  induction t with
  | zero =>
    exact ⟨[], fun _ _ => rfl⟩
  | succ t ih =>
    obtain ⟨touched, ht⟩ := ih
    refine ⟨(M.system.run t).head :: touched, ?_⟩
    intro pos hn
    have hne : pos ≠ (M.system.run t).head := by
      intro heq
      apply hn
      simp [heq]
    have hnot : pos ∉ touched := by
      intro hm
      apply hn
      simp [hm]
    change ((M.step (M.system.run t)).1).tape pos = M.blank
    simp [Machine.step, Config.write, hne, ht pos hnot]

end Shared.Beeping.Machines
