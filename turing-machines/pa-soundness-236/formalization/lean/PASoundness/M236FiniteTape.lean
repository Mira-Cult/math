import PASoundness.M236BootstrapFill

/-!
A finite zipper representation for the blank-background two-way tape. This
is intended as an executable certificate interface; a representation proof
must preserve all infinitely many blank cells, not only a finite window.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.FiniteTape

open Shared.Beeping Shared.Beeping.Machines PASoundness.M236.BootstrapScan

structure Tape where
  /-- Nearest cell strictly left of the head first. -/
  left : List Bool
  /-- Current cell first; omitted cells on either side are zero. -/
  right : List Bool
  deriving DecidableEq, Repr

def read (t : Tape) : Bool := t.right.headD false

def moveRight (t : Tape) (write : Bool) : Tape :=
  ⟨write :: t.left, t.right.drop 1⟩

def moveLeft (t : Tape) (write : Bool) : Tape :=
  ⟨t.left.drop 1, t.left.headD false :: write :: t.right.drop 1⟩

/-- The two clauses cover every integer position with no finite tape bound. -/
def Represents (t : Tape) {n : Nat} (c : Config n) : Prop :=
  (∀ i : Nat, c.tape (c.head + (i : Int)) = t.right.getD i false) ∧
  (∀ i : Nat, c.tape (c.head - (i : Int) - 1) = t.left.getD i false)

theorem blank_represents {n : Nat} (q : Fin n) (h : Int) :
    Represents ⟨[], []⟩ (⟨q, h, fun _ => false⟩ : Config n) := by
  constructor <;> intro i <;> simp

theorem represented_head {n : Nat} {t : Tape} {c : Config n}
    (h : Represents t c) : c.tape c.head = read t := by
  have h0 := h.1 0
  cases ht : t.right <;> simpa [read, ht] using h0

theorem getD_drop_one (xs : List Bool) (i : Nat) :
    (xs.drop 1).getD i false = xs.getD (i + 1) false := by
  cases xs <;> simp

theorem getD_head_drop (xs : List Bool) (i : Nat) :
    (xs.headD false :: xs.drop 1).getD i false = xs.getD i false := by
  cases xs <;> cases i <;> simp

theorem represents_right {n : Nat} {t : Tape} {c : Config n}
    (h : Represents t c) (b : Bool) :
    Represents (moveRight t b) (⟨c.state, c.head + 1, c.write b⟩ : Config n) := by
  constructor
  · intro i
    have hx : c.head + 1 + (i : Int) ≠ c.head := by omega
    have hp : c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) := by omega
    change c.write b (c.head + 1 + (i : Int)) = (t.right.drop 1).getD i false
    rw [Config.write_other _ _ _ hx, hp, h.1 (i + 1), getD_drop_one]
  · intro i
    cases i with
    | zero =>
      have hp : c.head + 1 - (0 : Int) - 1 = c.head := by omega
      change c.write b (c.head + 1 - (0 : Int) - 1) = (b :: t.left).getD 0 false
      rw [hp, Config.write_head]
      rfl
    | succ i =>
      have hx : c.head + 1 - ((i + 1 : Nat) : Int) - 1 ≠ c.head := by omega
      have hp : c.head + 1 - ((i + 1 : Nat) : Int) - 1 = c.head - (i : Int) - 1 := by omega
      change c.write b (c.head + 1 - ((i + 1 : Nat) : Int) - 1) =
        (b :: t.left).getD (i + 1) false
      rw [Config.write_other _ _ _ hx, hp, h.2 i]
      rfl

theorem represents_left {n : Nat} {t : Tape} {c : Config n}
    (h : Represents t c) (b : Bool) :
    Represents (moveLeft t b) (⟨c.state, c.head - 1, c.write b⟩ : Config n) := by
  constructor
  · intro i
    cases i with
    | zero =>
      have hx : c.head - 1 + (0 : Int) ≠ c.head := by omega
      have hp : c.head - 1 + (0 : Int) = c.head - (0 : Int) - 1 := by omega
      change c.write b (c.head - 1 + (0 : Int)) =
        (t.left.headD false :: b :: t.right.drop 1).getD 0 false
      have h0 := h.2 0
      simp only [Int.ofNat_zero] at h0
      rw [Config.write_other _ _ _ hx, hp, h0]
      cases ht : t.left <;> simp [ht]
    | succ i =>
      cases i with
      | zero =>
        have hp : c.head - 1 + (1 : Int) = c.head := by omega
        change c.write b (c.head - 1 + (1 : Int)) =
          (t.left.headD false :: b :: t.right.drop 1).getD 1 false
        rw [hp, Config.write_head]
        rfl
      | succ i =>
        have hx : c.head - 1 + ((i + 2 : Nat) : Int) ≠ c.head := by omega
        have hp : c.head - 1 + ((i + 2 : Nat) : Int) = c.head + ((i + 1 : Nat) : Int) := by omega
        change c.write b (c.head - 1 + ((i + 2 : Nat) : Int)) =
          (t.left.headD false :: b :: t.right.drop 1).getD (i + 2) false
        rw [Config.write_other _ _ _ hx, hp, h.1 (i + 1)]
        simpa using (getD_drop_one t.right i).symm
  · intro i
    have hx : c.head - 1 - (i : Int) - 1 ≠ c.head := by omega
    have hp : c.head - 1 - (i : Int) - 1 = c.head - ((i + 1 : Nat) : Int) - 1 := by omega
    change c.write b (c.head - 1 - (i : Int) - 1) = (t.left.drop 1).getD i false
    rw [Config.write_other _ _ _ hx, hp, h.2 (i + 1), getD_drop_one]

structure Configuration (n : Nat) where
  state : Fin n
  head : Int
  tape : Tape
  deriving DecidableEq, Repr

def Related {n : Nat} (z : Configuration n) (c : Config n) : Prop :=
  z.state = c.state ∧ z.head = c.head ∧ Represents z.tape c

/-- One executable zipper step uses the actual finite table and event labels. -/
def step {n : Nat} (m : Machine n) (labels : BitLabels n)
    (z : Configuration n) : Configuration n × List Bool :=
  let symbol := read z.tape
  let row := m.table.row z.state symbol
  let nextTape := match row.move with
    | .left => moveLeft z.tape row.write
    | .right => moveRight z.tape row.write
  (⟨row.next, row.move.apply z.head, nextTape⟩, (labels.at z.state symbol).toList)

/-- A checked zipper step agrees with the full infinite tape and with the
optional event on the actual row, in either movement direction. -/
theorem step_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    {z : Configuration n} {c : Config n} (h : Related z c) :
    Related (step m labels z).1 ((machineWordSystem m labels).step c).1 ∧
      (step m labels z).2 = ((machineWordSystem m labels).step c).2 := by
  rcases h with ⟨hq, hh, ht⟩
  have hs : read z.tape = c.tape c.head := (represented_head ht).symm
  cases he : (m.table.row c.state (c.tape c.head)).move with
  | left =>
    have hr := represents_left ht (m.table.row c.state (c.tape c.head)).write
    simp only [Related, step, machineWordSystem, Machine.step, hq, hh, hs]
    simp only [he, Move.apply, true_and, and_true]
    exact hr
  | right =>
    have hr := represents_right ht (m.table.row c.state (c.tape c.head)).write
    simp only [Related, step, machineWordSystem, Machine.step, hq, hh, hs]
    simp only [he, Move.apply, true_and, and_true]
    exact hr

def system {n : Nat} (m : Machine n) (labels : BitLabels n) :
    WordEventSystem (Configuration n) Bool where
  initial := ⟨m.start, m.startHead, ⟨[], []⟩⟩
  step := step m labels

theorem initial_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (blank : m.blank = false) :
    Related (system m labels).initial (machineWordSystem m labels).initial := by
  simp only [Related, system, machineWordSystem, Machine.initial]
  refine ⟨trivial, trivial, ?_⟩
  rw [blank]
  exact blank_represents _ _

/-- Every finite zipper execution is related to the actual full-tape
execution and has exactly the same ordered event word. -/
theorem advance_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    {z : Configuration n} {c : Config n} (h : Related z c) (t : Nat) :
    Related ((system m labels).advance z t) ((machineWordSystem m labels).advance c t) ∧
      (system m labels).wordFrom z t = (machineWordSystem m labels).wordFrom c t := by
  induction t with
  | zero => exact ⟨h, rfl⟩
  | succ t ih =>
    have hs := step_sound m labels ih.1
    constructor
    · exact hs.1
    · change (system m labels).wordFrom z t ++
          (step m labels ((system m labels).advance z t)).2 =
        (machineWordSystem m labels).wordFrom c t ++
          ((machineWordSystem m labels).step ((machineWordSystem m labels).advance c t)).2
      rw [ih.2, hs.2]

theorem run_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (blank : m.blank = false) (t : Nat) :
    Related ((system m labels).run t) ((machineWordSystem m labels).run t) ∧
      (system m labels).prefixWord t = (machineWordSystem m labels).prefixWord t :=
  advance_sound m labels (initial_sound m labels blank) t

theorem same_output {n : Nat} (m : Machine n) (labels : BitLabels n)
    (blank : m.blank = false) :
    SameOutput (system m labels) (machineWordSystem m labels) := by
  intro w
  constructor <;> rintro ⟨t, suffix, h⟩ <;> refine ⟨t, suffix, ?_⟩
  · rw [← (run_sound m labels blank t).2]
    exact h
  · rw [(run_sound m labels blank t).2]
    exact h

theorem selected_run_sound (t : Nat) :
    Related ((system machine machineLabels).run t)
      ((machineWordSystem machine machineLabels).run t) ∧
      (system machine machineLabels).prefixWord t =
        (machineWordSystem machine machineLabels).prefixWord t :=
  run_sound machine machineLabels rfl t

theorem raw_run_sound (t : Nat) :
    Related ((system raw rawLabels).run t)
      ((machineWordSystem raw rawLabels).run t) ∧
      (system raw rawLabels).prefixWord t = (machineWordSystem raw rawLabels).prefixWord t :=
  run_sound raw rawLabels rfl t

/-- An untrusted producer may provide these finite milestones. A milestone
includes the entire finite zipper tape and the exact intervening event word. -/
structure Checkpoint (n : Nat) where
  ticks : Nat
  finish : Configuration n
  output : List Bool
  deriving DecidableEq, Repr

def totalTicks {n : Nat} : List (Checkpoint n) → Nat
  | [] => 0
  | p :: ps => p.ticks + totalTicks ps

def finalConfig {n : Nat} (start : Configuration n) : List (Checkpoint n) → Configuration n
  | [] => start
  | p :: ps => finalConfig p.finish ps

def totalOutput {n : Nat} : List (Checkpoint n) → List Bool
  | [] => []
  | p :: ps => p.output ++ totalOutput ps

/-- Every asserted segment must take positive time and match both its full
finite endpoint and its complete event word. -/
def check {n : Nat} (m : Machine n) (labels : BitLabels n) :
    Configuration n → List (Checkpoint n) → Bool
  | _, [] => true
  | start, p :: ps =>
    decide (0 < p.ticks) &&
      decide ((system m labels).advance start p.ticks = p.finish) &&
      decide ((system m labels).wordFrom start p.ticks = p.output) &&
      check m labels p.finish ps

theorem check_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (ps : List (Checkpoint n)) (start : Configuration n)
    (h : check m labels start ps = true) :
    (system m labels).Block start (totalTicks ps) (finalConfig start ps) (totalOutput ps) := by
  induction ps generalizing start with
  | nil => exact WordEventSystem.Block.refl (system m labels) start
  | cons p ps ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    have hblock : (system m labels).Block start p.ticks p.finish p.output := ⟨h.1.1.2, h.1.2⟩
    have htail := ih p.finish h.2
    exact hblock.trans (system m labels) htail

theorem check_positive {n : Nat} (m : Machine n) (labels : BitLabels n)
    (ps : List (Checkpoint n)) (start : Configuration n)
    (h : check m labels start ps = true) : ∀ p ∈ ps, 0 < p.ticks := by
  induction ps generalizing start with
  | nil => simp
  | cons p ps ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1.1.1
    · exact ih p.finish h.2 x hx

/-- Certificate acceptance implies the asserted full-tape relation and
ordered output for the literal blank-start run. -/
theorem selected_certificate_sound (ps : List (Checkpoint 236))
    (h : check machine machineLabels (system machine machineLabels).initial ps = true) :
    Related (finalConfig (system machine machineLabels).initial ps)
        ((machineWordSystem machine machineLabels).run (totalTicks ps)) ∧
      totalOutput ps = (machineWordSystem machine machineLabels).prefixWord (totalTicks ps) := by
  have hb := check_sound machine machineLabels ps _ h
  have hs := selected_run_sound (totalTicks ps)
  change Related ((system machine machineLabels).advance _ (totalTicks ps)) _ ∧
    (system machine machineLabels).wordFrom _ (totalTicks ps) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  exact hs

theorem raw_certificate_sound (ps : List (Checkpoint 237))
    (h : check raw rawLabels (system raw rawLabels).initial ps = true) :
    Related (finalConfig (system raw rawLabels).initial ps)
        ((machineWordSystem raw rawLabels).run (totalTicks ps)) ∧
      totalOutput ps = (machineWordSystem raw rawLabels).prefixWord (totalTicks ps) := by
  have hb := check_sound raw rawLabels ps _ h
  have hs := raw_run_sound (totalTicks ps)
  change Related ((system raw rawLabels).advance _ (totalTicks ps)) _ ∧
    (system raw rawLabels).wordFrom _ (totalTicks ps) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  exact hs

/-- Small regression controls for blank startup and the zero-background
convention. The general simulation theorem does not depend on these fixtures. -/
example : (system machine machineLabels).run 3 =
    ⟨75, -1, ⟨[], [false, true, false]⟩⟩ := by decide

example : (system machine machineLabels).run 3 ≠
    ⟨75, -1, ⟨[], [true, true, false]⟩⟩ := by decide

example : (system machine machineLabels).prefixWord 3 = [] := by decide

def selectedThree : List (Checkpoint 236) :=
  [⟨3, ⟨75, -1, ⟨[], [false, true, false]⟩⟩, []⟩]

example : check machine machineLabels (system machine machineLabels).initial selectedThree = true := by decide

example : check machine machineLabels (system machine machineLabels).initial
    [⟨3, ⟨75, -1, ⟨[], [false, true, false]⟩⟩, [false]⟩] = false := by decide

example : check machine machineLabels (system machine machineLabels).initial
    [⟨0, (system machine machineLabels).initial, []⟩] = false := by decide

theorem selected_three_from_blank :
    Related ⟨75, -1, ⟨[], [false, true, false]⟩⟩
      ((machineWordSystem machine machineLabels).run 3) ∧
      (machineWordSystem machine machineLabels).prefixWord 3 = [] := by
  have h := selected_certificate_sound selectedThree (by decide)
  simpa [selectedThree, totalTicks, finalConfig, totalOutput] using h

def selectedHundred : List (Checkpoint 236) :=
  [⟨100, ⟨74, -16, ⟨[], [true, true, false, true, false, true, false, true,
    false, true, false, true, false, true, true, true, false, true, true]⟩⟩, []⟩]

/-- A finite regression check of the selected blank start, including the whole
infinite zero background. It is not an omega-acceptance result. -/
theorem selected_hundred_from_blank :
    Related (finalConfig (system machine machineLabels).initial selectedHundred)
      ((machineWordSystem machine machineLabels).run 100) ∧
      (machineWordSystem machine machineLabels).prefixWord 100 = [] := by
  have h := selected_certificate_sound selectedHundred (by decide)
  simpa [selectedHundred, totalTicks, finalConfig, totalOutput] using h

end PASoundness.M236.FiniteTape
