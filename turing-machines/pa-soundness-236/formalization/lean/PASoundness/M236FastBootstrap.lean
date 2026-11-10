import PASoundness.M236FiniteTape

/-!
Checked accelerated steps for finite bootstrap certificates. A shortcut is
permitted only when its concrete tape pattern is checked, and its soundness
theorem accounts for the exact positive number of literal transitions.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.FastBootstrap

open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape

def rawSystem := system raw rawLabels

def rightNext (t : Tape) : Tape := moveRight (moveRight t true) false

/-- Scan exactly n `1,0` pairs, rejecting any disagreement. The final tape
retains the finite zipper's whole left and right lists, including zeros. -/
def scanRight : Nat → Tape → Option Tape
  | 0, t => some t
  | n + 1, t =>
      if read t = true ∧ read (moveRight t true) = false then
        scanRight n (rightNext t)
      else none

theorem first_right (h : Int) (t : Tape) (hr : read t = true) :
    rawSystem.step ⟨77, h, t⟩ = (⟨78, h + 1, moveRight t true⟩, []) := by
  have row : raw.table.row 77 true = ⟨true, .right, 78, false⟩ := by decide
  have event : rawLabels.at 77 true = none := by decide
  simp [rawSystem, system, step, hr, row, event, Move.apply]

theorem second_right (h : Int) (t : Tape) (hr : read t = false) :
    rawSystem.step ⟨78, h, t⟩ = (⟨77, h + 1, moveRight t false⟩, []) := by
  have row : raw.table.row 78 false = ⟨false, .right, 77, false⟩ := by decide
  have event : rawLabels.at 78 false = none := by decide
  simp [rawSystem, system, step, hr, row, event, Move.apply]

theorem right_pair (h : Int) (t : Tape)
    (h1 : read t = true) (h0 : read (moveRight t true) = false) :
    rawSystem.Block ⟨77, h, t⟩ 2 ⟨77, h + 2, rightNext t⟩ [] := by
  have ha := WordEventSystem.Block.single rawSystem (first_right h t h1)
  have hb := WordEventSystem.Block.single rawSystem (second_right (h + 1) (moveRight t true) h0)
  have he : h + 1 + 1 = h + 2 := by omega
  simpa [he, rightNext] using ha.trans rawSystem hb

theorem scanRight_sound (n : Nat) (h : Int) (t out : Tape)
    (hs : scanRight n t = some out) :
    rawSystem.Block ⟨77, h, t⟩ (2 * n) ⟨77, h + 2 * (n : Int), out⟩ [] := by
  induction n generalizing h t with
  | zero =>
    simp only [scanRight, Option.some.injEq] at hs
    subst out
    simpa using WordEventSystem.Block.refl rawSystem ⟨77, h, t⟩
  | succ n ih =>
    simp only [scanRight] at hs
    split at hs
    · rename_i hp
      have hfirst := right_pair h t hp.1 hp.2
      have hrest := ih (h + 2) (rightNext t) hs
      have hwhole := hfirst.trans rawSystem hrest
      have he : h + 2 + 2 * (n : Int) = h + 2 * ((n + 1 : Nat) : Int) := by omega
      have ht : 2 + 2 * n = 2 * (n + 1) := by omega
      simpa only [List.nil_append, he, ht] using hwhole
    · contradiction

def leftNext (t : Tape) : Tape := moveLeft (moveLeft t false) true

def scanLeft : Nat → Tape → Option Tape
  | 0, t => some t
  | n + 1, t =>
      if read t = true ∧ read (moveLeft t false) = false then
        scanLeft n (leftNext t)
      else none

theorem first_left (h : Int) (t : Tape) (hr : read t = true) :
    rawSystem.step ⟨75, h, t⟩ = (⟨77, h - 1, moveLeft t false⟩, []) := by
  have row : raw.table.row 75 true = ⟨false, .left, 77, false⟩ := by decide
  have event : rawLabels.at 75 true = none := by decide
  simp [rawSystem, system, step, hr, row, event, Move.apply]

theorem second_left (h : Int) (t : Tape) (hr : read t = false) :
    rawSystem.step ⟨77, h, t⟩ = (⟨75, h - 1, moveLeft t true⟩, []) := by
  have row : raw.table.row 77 false = ⟨true, .left, 75, false⟩ := by decide
  have event : rawLabels.at 77 false = none := by decide
  simp [rawSystem, system, step, hr, row, event, Move.apply]

theorem left_pair (h : Int) (t : Tape)
    (h1 : read t = true) (h0 : read (moveLeft t false) = false) :
    rawSystem.Block ⟨75, h, t⟩ 2 ⟨75, h - 2, leftNext t⟩ [] := by
  have ha := WordEventSystem.Block.single rawSystem (first_left h t h1)
  have hb := WordEventSystem.Block.single rawSystem (second_left (h - 1) (moveLeft t false) h0)
  have he : h - 1 - 1 = h - 2 := by omega
  simpa [he, leftNext] using ha.trans rawSystem hb

theorem scanLeft_sound (n : Nat) (h : Int) (t out : Tape)
    (hs : scanLeft n t = some out) :
    rawSystem.Block ⟨75, h, t⟩ (2 * n) ⟨75, h - 2 * (n : Int), out⟩ [] := by
  induction n generalizing h t with
  | zero =>
    simp only [scanLeft, Option.some.injEq] at hs
    subst out
    simpa using WordEventSystem.Block.refl rawSystem ⟨75, h, t⟩
  | succ n ih =>
    simp only [scanLeft] at hs
    split at hs
    · rename_i hp
      have hfirst := left_pair h t hp.1 hp.2
      have hrest := ih (h - 2) (leftNext t) hs
      have hwhole := hfirst.trans rawSystem hrest
      have he : h - 2 - 2 * (n : Int) = h - 2 * ((n + 1 : Nat) : Int) := by omega
      have ht : 2 + 2 * n = 2 * (n + 1) := by omega
      simpa only [List.nil_append, he, ht] using hwhole
    · contradiction

def fillNext (t : Tape) : Tape := moveLeft (moveLeft t true) true

def scanFill : Nat → Tape → Option Tape
  | 0, t => some t
  | n + 1, t =>
      if read t = true ∧ read (moveLeft t true) = false then
        scanFill n (fillNext t)
      else none

theorem first_fill (h : Int) (t : Tape) (hr : read t = true) :
    rawSystem.step ⟨0, h, t⟩ = (⟨76, h - 1, moveLeft t true⟩, []) := by
  have row : raw.table.row 0 true = ⟨true, .left, 76, false⟩ := by decide
  have event : rawLabels.at 0 true = none := by decide
  simp [rawSystem, system, step, hr, row, event, Move.apply]

theorem second_fill (h : Int) (t : Tape) (hr : read t = false) :
    rawSystem.step ⟨76, h, t⟩ = (⟨0, h - 1, moveLeft t true⟩, []) := by
  have row : raw.table.row 76 false = ⟨true, .left, 0, false⟩ := by decide
  have event : rawLabels.at 76 false = none := by decide
  simp [rawSystem, system, step, hr, row, event, Move.apply]

theorem fill_pair (h : Int) (t : Tape)
    (h1 : read t = true) (h0 : read (moveLeft t true) = false) :
    rawSystem.Block ⟨0, h, t⟩ 2 ⟨0, h - 2, fillNext t⟩ [] := by
  have ha := WordEventSystem.Block.single rawSystem (first_fill h t h1)
  have hb := WordEventSystem.Block.single rawSystem (second_fill (h - 1) (moveLeft t true) h0)
  have he : h - 1 - 1 = h - 2 := by omega
  simpa [he, fillNext] using ha.trans rawSystem hb

theorem scanFill_sound (n : Nat) (h : Int) (t out : Tape)
    (hs : scanFill n t = some out) :
    rawSystem.Block ⟨0, h, t⟩ (2 * n) ⟨0, h - 2 * (n : Int), out⟩ [] := by
  induction n generalizing h t with
  | zero =>
    simp only [scanFill, Option.some.injEq] at hs
    subst out
    simpa using WordEventSystem.Block.refl rawSystem ⟨0, h, t⟩
  | succ n ih =>
    simp only [scanFill] at hs
    split at hs
    · rename_i hp
      have hfirst := fill_pair h t hp.1 hp.2
      have hrest := ih (h - 2) (fillNext t) hs
      have hwhole := hfirst.trans rawSystem hrest
      have he : h - 2 - 2 * (n : Int) = h - 2 * ((n + 1 : Nat) : Int) := by omega
      have ht : 2 + 2 * n = 2 * (n + 1) := by omega
      simpa only [List.nil_append, he, ht] using hwhole
    · contradiction

/-- A certificate consists of literal single steps and checked scan counts.
Every operation is required to advance physical time. -/
inductive Op where
  | one
  | right (pairs : Nat)
  | left (pairs : Nat)
  | fill (pairs : Nat)
  deriving DecidableEq, Repr

def perform (op : Op) (z : Configuration 237) :
    Option (Configuration 237 × Nat × List Bool) :=
  match op with
  | .one => some ((rawSystem.step z).1, 1, (rawSystem.step z).2)
  | .right n =>
      if 0 < n ∧ z.state = 77 then
        (scanRight n z.tape).map fun out => (⟨77, z.head + 2 * (n : Int), out⟩, 2 * n, [])
      else none
  | .left n =>
      if 0 < n ∧ z.state = 75 then
        (scanLeft n z.tape).map fun out => (⟨75, z.head - 2 * (n : Int), out⟩, 2 * n, [])
      else none
  | .fill n =>
      if 0 < n ∧ z.state = 0 then
        (scanFill n z.tape).map fun out => (⟨0, z.head - 2 * (n : Int), out⟩, 2 * n, [])
      else none

theorem perform_sound (op : Op) (z out : Configuration 237) (ticks : Nat) (word : List Bool)
    (h : perform op z = some (out, ticks, word)) :
    rawSystem.Block z ticks out word ∧ 0 < ticks := by
  cases op with
  | one =>
    simp only [perform, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨WordEventSystem.Block.single rawSystem rfl, by omega⟩
  | right n =>
    simp only [perform] at h
    split at h
    · rename_i hg
      cases hs : scanRight n z.tape with
      | none => simp [hs] at h
      | some t =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        cases z with
        | mk q head tape =>
          simp only at hg hs ⊢
          rcases hg with ⟨hn, hq⟩
          subst q
          exact ⟨scanRight_sound n head tape t hs, by omega⟩
    · contradiction

  | left n =>
    simp only [perform] at h
    split at h
    · rename_i hg
      cases hs : scanLeft n z.tape with
      | none => simp [hs] at h
      | some t =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        cases z with
        | mk q head tape =>
          simp only at hg hs ⊢
          rcases hg with ⟨hn, hq⟩
          subst q
          exact ⟨scanLeft_sound n head tape t hs, by omega⟩
    · contradiction
  | fill n =>
    simp only [perform] at h
    split at h
    · rename_i hg
      cases hs : scanFill n z.tape with
      | none => simp [hs] at h
      | some t =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        cases z with
        | mk q head tape =>
          simp only at hg hs ⊢
          rcases hg with ⟨hn, hq⟩
          subst q
          exact ⟨scanFill_sound n head tape t hs, by omega⟩
    · contradiction


/-- Execute a finite, untrusted program of literal steps and checked sweeps.
The returned count and event list include every represented transition. -/
def runOps : Configuration 237 → List Op → Option (Configuration 237 × Nat × List Bool)
  | z, [] => some (z, 0, [])
  | z, op :: ops => do
      let (middle, ticks, first) ← perform op z
      let (finish, rest, second) ← runOps middle ops
      pure (finish, ticks + rest, first ++ second)

theorem runOps_sound (ops : List Op) (start finish : Configuration 237)
    (ticks : Nat) (word : List Bool) (h : runOps start ops = some (finish, ticks, word)) :
    rawSystem.Block start ticks finish word ∧ (ops ≠ [] → 0 < ticks) := by
  induction ops generalizing start finish ticks word with
  | nil =>
    simp only [runOps, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨WordEventSystem.Block.refl rawSystem start, by simp⟩
  | cons op ops ih =>
    cases hp : perform op start with
    | none => simp [runOps, hp] at h
    | some p =>
      rcases p with ⟨middle, dt, first⟩
      cases ht : runOps middle ops with
      | none => simp [runOps, hp, ht] at h
      | some p =>
        rcases p with ⟨final, rest, second⟩
        simp [runOps, hp, ht] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        have hb := perform_sound op start middle dt first hp
        have hr := ih middle final rest second ht
        refine ⟨hb.1.trans rawSystem hr.1, ?_⟩
        intro _
        omega

/-- Successful execution from the literal blank start yields a finite-tape
representation of the actual raw configuration and the exact output prefix
of both the raw table and the 236-state quotient. -/
theorem blank_program_sound (ops : List Op) (finish : Configuration 237)
    (ticks : Nat) (word : List Bool)
    (h : runOps rawSystem.initial ops = some (finish, ticks, word)) :
    Related finish ((machineWordSystem raw rawLabels).run ticks) ∧
      (machineWordSystem raw rawLabels).prefixWord ticks = word ∧
      (machineWordSystem machine machineLabels).prefixWord ticks = word ∧
      (ops ≠ [] → 0 < ticks) := by
  have hb := runOps_sound ops rawSystem.initial finish ticks word h
  have hr := raw_run_sound ticks
  change Related (rawSystem.advance rawSystem.initial ticks) _ ∧
    rawSystem.wordFrom rawSystem.initial ticks = _ at hr
  rw [hb.1.endpoint, hb.1.output] at hr
  refine ⟨hr.1, hr.2.symm, ?_, hb.2⟩
  rw [← prefix_eq ticks]
  exact hr.2.symm

end PASoundness.M236.FastBootstrap
