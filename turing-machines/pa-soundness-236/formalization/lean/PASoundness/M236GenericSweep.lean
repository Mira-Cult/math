import PASoundness.M236FiniteTape

/-!
Generic checked two-row sweeps over the finite tape representation. The
actual table and event labels remain explicit inputs; no source-level
behavior or initialization assumption is hidden in the interface.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.GenericSweep

open Shared.Beeping Shared.Beeping.Machines PASoundness.M236.FiniteTape

def move (direction : Move) (t : Tape) (symbol : Bool) : Tape :=
  match direction with
  | .left => moveLeft t symbol
  | .right => moveRight t symbol

def position (direction : Move) (head : Int) (pairs : Nat) : Int :=
  match direction with
  | .left => head - 2 * (pairs : Int)
  | .right => head + 2 * (pairs : Int)

/-- The two literal rows return to the starting state, move in the same
direction, and emit no event. The writes may be arbitrary. -/
def Valid {n : Nat} (m : Machine n) (labels : BitLabels n)
    (q : Fin n) (first second : Bool) (direction : Move) : Prop :=
  let a := m.table.row q first
  let b := m.table.row a.next second
  a.move = direction ∧ b.move = direction ∧ b.next = q ∧
    labels.at q first = none ∧ labels.at a.next second = none

instance {n : Nat} (m : Machine n) (labels : BitLabels n)
    (q : Fin n) (first second : Bool) (direction : Move) :
    Decidable (Valid m labels q first second direction) := by
  unfold Valid
  infer_instance

def pairNext {n : Nat} (m : Machine n) (q : Fin n) (first second : Bool)
    (direction : Move) (t : Tape) : Tape :=
  let a := m.table.row q first
  let b := m.table.row a.next second
  move direction (move direction t a.write) b.write

/-- Check all visited symbols while computing the finite-tape endpoint. -/
def scan {n : Nat} (m : Machine n) (q : Fin n) (first second : Bool)
    (direction : Move) : Nat → Tape → Option Tape
  | 0, t => some t
  | k + 1, t =>
      let a := m.table.row q first
      if read t = first ∧ read (move direction t a.write) = second then
        scan m q first second direction k (pairNext m q first second direction t)
      else none

theorem one {n : Nat} (m : Machine n) (labels : BitLabels n)
    (q : Fin n) (h : Int) (t : Tape) (symbol : Bool)
    (hr : read t = symbol) :
    (system m labels).step ⟨q, h, t⟩ =
      (⟨(m.table.row q symbol).next, (m.table.row q symbol).move.apply h,
        move (m.table.row q symbol).move t (m.table.row q symbol).write⟩,
        (labels.at q symbol).toList) := by
  cases hd : (m.table.row q symbol).move <;>
    simp [system, step, hr, hd, move]

theorem pair_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (q : Fin n) (first second : Bool) (direction : Move) (h : Int) (t : Tape)
    (hv : Valid m labels q first second direction)
    (hfirst : read t = first)
    (hsecond : read (move direction t (m.table.row q first).write) = second) :
    (system m labels).Block ⟨q, h, t⟩ 2
      ⟨q, position direction h 1, pairNext m q first second direction t⟩ [] := by
  rcases hv with ⟨ha, hb, hq, he0, he1⟩
  have hstep0 := one m labels q h t first hfirst
  rw [ha, he0] at hstep0
  have hstep1 := one m labels (m.table.row q first).next (direction.apply h)
    (move direction t (m.table.row q first).write) second hsecond
  rw [hb, hq, he1] at hstep1
  have hblock := (WordEventSystem.Block.single (system m labels) hstep0).trans
    (system m labels) (WordEventSystem.Block.single (system m labels) hstep1)
  cases direction with
  | left =>
    have he : h - 1 - 1 = h - 2 := by omega
    simpa [position, pairNext, Move.apply, he] using hblock
  | right =>
    have he : h + 1 + 1 = h + 2 := by omega
    simpa [position, pairNext, Move.apply, he] using hblock

theorem scan_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (q : Fin n) (first second : Bool) (direction : Move)
    (hv : Valid m labels q first second direction)
    (pairs : Nat) (h : Int) (t out : Tape)
    (hs : scan m q first second direction pairs t = some out) :
    (system m labels).Block ⟨q, h, t⟩ (2 * pairs)
      ⟨q, position direction h pairs, out⟩ [] := by
  induction pairs generalizing h t with
  | zero =>
    simp only [scan, Option.some.injEq] at hs
    subst out
    cases direction <;> simpa [position] using WordEventSystem.Block.refl (system m labels) ⟨q, h, t⟩
  | succ pairs ih =>
    simp only [scan] at hs
    split at hs
    · rename_i hp
      have hfirst := pair_sound m labels q first second direction h t hv hp.1 hp.2
      have hrest := ih (position direction h 1) (pairNext m q first second direction t) hs
      have hwhole := hfirst.trans (system m labels) hrest
      have ht : 2 + 2 * pairs = 2 * (pairs + 1) := by omega
      cases direction with
      | left =>
        simp only [position] at hwhole ⊢
        have he : h - 2 * (1 : Int) - 2 * (pairs : Int) =
            h - 2 * ((pairs + 1 : Nat) : Int) := by omega
        simpa only [List.nil_append, Int.ofNat_one, ht, he] using hwhole
      | right =>
        simp only [position] at hwhole ⊢
        have he : h + 2 * (1 : Int) + 2 * (pairs : Int) =
            h + 2 * ((pairs + 1 : Nat) : Int) := by omega
        simpa only [List.nil_append, Int.ofNat_one, ht, he] using hwhole
    · cases hs

structure Instruction (n : Nat) where
  state : Fin n
  first : Bool
  second : Bool
  direction : Move
  pairs : Nat
  deriving DecidableEq, Repr

/-- The checker rejects an invalid row pair, wrong starting state, wrong
tape pattern, and a zero-duration sweep. -/
def perform {n : Nat} (m : Machine n) (labels : BitLabels n)
    (instruction : Instruction n) (z : Configuration n) :
    Option (Configuration n × Nat × List Bool) :=
  if 0 < instruction.pairs ∧ z.state = instruction.state ∧
      Valid m labels instruction.state instruction.first instruction.second instruction.direction then
    (scan m instruction.state instruction.first instruction.second instruction.direction
      instruction.pairs z.tape).map fun out =>
      (⟨instruction.state, position instruction.direction z.head instruction.pairs, out⟩,
        2 * instruction.pairs, [])
  else none

theorem perform_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (instruction : Instruction n) (z out : Configuration n) (ticks : Nat) (word : List Bool)
    (h : perform m labels instruction z = some (out, ticks, word)) :
    (system m labels).Block z ticks out word ∧ 0 < ticks := by
  simp only [perform] at h
  split at h
  · rename_i hg
    cases hs : scan m instruction.state instruction.first instruction.second instruction.direction
        instruction.pairs z.tape with
    | none => simp [hs] at h
    | some t =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      cases z with
      | mk q head tape =>
        simp only at hg hs ⊢
        rcases hg with ⟨hn, hq, hv⟩
        subst q
        exact ⟨scan_sound m labels instruction.state instruction.first instruction.second
          instruction.direction hv instruction.pairs head tape t hs, by omega⟩
  · contradiction

/-- Each accepted shortcut is a positive-length block of the actual full
two-way tape machine with exactly the same event word. -/
theorem physical_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (instruction : Instruction n) (z out : Configuration n) (c : Config n)
    (ticks : Nat) (word : List Bool) (hr : Related z c)
    (hc : perform m labels instruction z = some (out, ticks, word)) :
    ∃ finish, (machineWordSystem m labels).Block c ticks finish word ∧
      Related out finish ∧ 0 < ticks := by
  have hb := perform_sound m labels instruction z out ticks word hc
  have hs := advance_sound m labels hr ticks
  rw [hb.1.endpoint, hb.1.output] at hs
  refine ⟨(machineWordSystem m labels).advance c ticks, ?_, hs.1, hb.2⟩
  exact ⟨rfl, hs.2.symm⟩

example : Valid raw rawLabels 1 true false .right := by decide
example : Valid raw rawLabels 35 false true .left := by decide
example : Valid raw rawLabels 64 true true .left := by decide
example : ¬ Valid raw rawLabels 1 true false .left := by decide

def markedControl : BitLabels 237 :=
  BitLabels.ofFn fun q b => if q = 1 ∧ b = true then some true else rawLabels.at q b

example : ¬ Valid raw markedControl 1 true false .right := by decide

example : perform raw rawLabels ⟨1, true, false, .right, 1⟩
    ⟨1, 0, ⟨[], [true, false]⟩⟩ =
    some (⟨1, 2, ⟨[false, true], []⟩⟩, 2, []) := by decide

example : perform raw rawLabels ⟨1, true, false, .right, 0⟩
    ⟨1, 0, ⟨[], [true, false]⟩⟩ = none := by decide

end PASoundness.M236.GenericSweep
