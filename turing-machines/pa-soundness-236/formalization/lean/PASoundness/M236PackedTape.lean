import PASoundness.M236BulkSweep

/-!
A compact finite zipper for long periodic stretches of the actual tape.
Its decoding is explicit: compressed data are only an efficiency device,
and the theorems below relate them to the complete finite zipper, including
its implicit blank background. No arithmetic or runtime invariant is assumed.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.PackedTape

open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.BulkSweep

inductive Chunk where
  | bit : Bool → Chunk
  | pair : Bool → Bool → Nat → Chunk
  deriving DecidableEq, Repr

def decode : List Chunk → List Bool
  | [] => []
  | .bit b :: rest => b :: decode rest
  | .pair a b n :: rest => pairs a b n ++ decode rest

theorem pairs_add (a b : Bool) (n k : Nat) :
    pairs a b (n + k) = pairs a b n ++ pairs a b k := by
  induction n with
  | zero => simp [pairs]
  | succ n ih => simp [pairs, ih, Nat.succ_add]

/-- Adjacent equal pair runs are merged without scanning their contents. -/
def prependPairs (a b : Bool) (n : Nat) (cs : List Chunk) : List Chunk :=
  if n = 0 then cs else
    match cs with
    | .pair x y k :: rest =>
      if a = x ∧ b = y then .pair a b (n + k) :: rest
      else .pair a b n :: cs
    | _ => .pair a b n :: cs

theorem decode_prependPairs (a b : Bool) (n : Nat) (cs : List Chunk) :
    decode (prependPairs a b n cs) = pairs a b n ++ decode cs := by
  cases cs with
  | nil => cases n <;> simp [prependPairs, decode, pairs]
  | cons c cs =>
    cases c with
    | bit x => cases n <;> simp [prependPairs, decode, pairs]
    | pair x y k =>
      by_cases hn : n = 0
      · simp [prependPairs, hn, pairs]
      · by_cases he : a = x ∧ b = y
        · rcases he with ⟨rfl, rfl⟩
          simp [prependPairs, hn, decode, pairs_add, List.append_assoc]
        · simp [prependPairs, hn, he, decode]

def prependBit (b : Bool) (cs : List Chunk) : List Chunk :=
  match cs with
  | .bit x :: rest => prependPairs b x 1 rest
  | _ => .bit b :: cs

theorem decode_prependBit (b : Bool) (cs : List Chunk) :
    decode (prependBit b cs) = b :: decode cs := by
  cases cs with
  | nil => rfl
  | cons c cs => cases c <;> simp [prependBit, decode, decode_prependPairs, pairs]

def pop : List Chunk → Bool × List Chunk
  | [] => (false, [])
  | .bit b :: rest => (b, rest)
  | .pair _ _ 0 :: rest => pop rest
  | .pair a b (n + 1) :: rest => (a, .bit b :: .pair a b n :: rest)

/-- Removing a packed bit agrees exactly with the zipper's read and drop,
including the default zero past its finite support. -/
theorem pop_decode (cs : List Chunk) :
    (pop cs).1 = (decode cs).headD false ∧
      decode (pop cs).2 = (decode cs).drop 1 := by
  induction cs with
  | nil => simp [pop, decode]
  | cons c cs ih =>
    cases c with
    | bit b => simp [pop, decode]
    | pair a b n =>
      cases n with
      | zero => simpa [pop, decode, pairs] using ih
      | succ n => simp [pop, decode, pairs]

def hasHead : List Chunk → Bool
  | [] => false
  | .bit _ :: _ => true
  | .pair _ _ 0 :: rest => hasHead rest
  | .pair _ _ (_ + 1) :: _ => true

theorem decode_pop_cons (cs : List Chunk) (h : hasHead cs = true) :
    decode cs = (pop cs).1 :: decode (pop cs).2 := by
  induction cs with
  | nil => simp [hasHead] at h
  | cons c cs ih =>
    cases c with
    | bit b => rfl
    | pair a b n =>
      cases n with
      | zero => simpa [hasHead, pop, decode, pairs] using ih (by simpa [hasHead] using h)
      | succ n => simp [pop, decode, pairs]

structure Tape where
  left : List Chunk
  right : List Chunk
  deriving DecidableEq, Repr

def unpack (t : Tape) : FiniteTape.Tape := ⟨decode t.left, decode t.right⟩

structure Configuration (n : Nat) where
  state : Fin n
  head : Int
  tape : Tape
  deriving DecidableEq, Repr

def unpackConfig {n : Nat} (c : Configuration n) : FiniteTape.Configuration n :=
  ⟨c.state, c.head, unpack c.tape⟩

def step {n : Nat} (m : Machine n) (labels : BitLabels n)
    (c : Configuration n) : Configuration n × List Bool :=
  let (symbol, right) := pop c.tape.right
  let row := m.table.row c.state symbol
  let nextTape := match row.move with
    | .right => ⟨prependBit row.write c.tape.left, right⟩
    | .left =>
      let (newHead, left) := pop c.tape.left
      ⟨left, prependBit newHead (prependBit row.write right)⟩
  (⟨row.next, row.move.apply c.head, nextTape⟩, (labels.at c.state symbol).toList)

theorem step_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (c : Configuration n) :
    unpackConfig (step m labels c).1 = (FiniteTape.step m labels (unpackConfig c)).1 ∧
      (step m labels c).2 = (FiniteTape.step m labels (unpackConfig c)).2 := by
  have hr := pop_decode c.tape.right
  have hl := pop_decode c.tape.left
  simp only [List.headD_eq_head?_getD] at hr hl
  cases hd : (m.table.row c.state (pop c.tape.right).1).move <;>
    simp [step, FiniteTape.step, unpackConfig, unpack, FiniteTape.read,
      moveRight, moveLeft, decode_prependBit, ← hr.1, ← hr.2, ← hl.1, ← hl.2, hd]

/-- Skip a positive number of checked pairs at the front of the right tape.
The count is bounded by the recorded run, and the row/event conditions are
checked against the machine itself. -/
def sweepRight {n : Nat} (m : Machine n) (labels : BitLabels n)
    (count : Nat) (c : Configuration n) : Option (Configuration n) :=
  match c.tape.right with
  | .pair first second k :: rest =>
    if 0 < count ∧ count ≤ k ∧
        GenericSweep.Valid m labels c.state first second .right then
      let a := m.table.row c.state first
      let b := m.table.row a.next second
      some ⟨c.state, c.head + 2 * (count : Int),
        ⟨prependPairs b.write a.write count c.tape.left,
          .pair first second (k - count) :: rest⟩⟩
    else none
  | _ => none

theorem sweepRight_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (count : Nat) (c out : Configuration n)
    (h : sweepRight m labels count c = some out) :
    (FiniteTape.system m labels).Block (unpackConfig c) (2 * count) (unpackConfig out) [] := by
  cases c with
  | mk q head tape =>
    cases tape with
    | mk left right =>
      cases right with
      | nil => simp [sweepRight] at h
      | cons chunk rest =>
        cases chunk with
        | bit bit => simp [sweepRight] at h
        | pair first second k =>
          simp only [sweepRight] at h
          split at h
          · rename_i hg
            simp only [Option.some.injEq] at h
            subst out
            have hs := right_block m labels q first second hg.2.2 count head
              (decode left) (pairs first second (k - count) ++ decode rest)
            have hk : k = count + (k - count) := by omega
            have hdecode : pairs first second k ++ decode rest =
                pairs first second count ++ (pairs first second (k - count) ++ decode rest) := by
              calc
                _ = pairs first second (count + (k - count)) ++ decode rest :=
                  congrArg (fun j => pairs first second j ++ decode rest) hk
                _ = _ := by rw [pairs_add, List.append_assoc]
            simpa only [unpackConfig, unpack, decode, decode_prependPairs, hdecode] using hs
          · cases h

/-- The mirrored shortcut checks an explicit current cell and a left-side
pair run. It does not manufacture a zero when the finite list has no head. -/
def sweepLeft {n : Nat} (m : Machine n) (labels : BitLabels n)
    (count : Nat) (c : Configuration n) : Option (Configuration n) :=
  match c.tape.left with
  | .pair second first k :: rest =>
    let (symbol, right) := pop c.tape.right
    if hasHead c.tape.right = true ∧ symbol = first ∧ 0 < count ∧ count ≤ k ∧
        GenericSweep.Valid m labels c.state first second .left then
      let a := m.table.row c.state first
      let b := m.table.row a.next second
      some ⟨c.state, c.head - 2 * (count : Int),
        ⟨.pair second first (k - count) :: rest,
          prependBit first (prependPairs b.write a.write count right)⟩⟩
    else none
  | _ => none

theorem sweepLeft_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (count : Nat) (c out : Configuration n)
    (h : sweepLeft m labels count c = some out) :
    (FiniteTape.system m labels).Block (unpackConfig c) (2 * count) (unpackConfig out) [] := by
  cases c with
  | mk q head tape =>
    cases tape with
    | mk left right =>
      cases left with
      | nil => simp [sweepLeft] at h
      | cons chunk rest =>
        cases chunk with
        | bit bit => simp [sweepLeft] at h
        | pair second first k =>
          simp only [sweepLeft] at h
          split at h
          · rename_i hg
            simp only [Option.some.injEq] at h
            subst out
            have hs := left_block m labels q first second hg.2.2.2.2 count head
              (pairs second first (k - count) ++ decode rest) (decode (pop right).2)
            have hk : k = count + (k - count) := by omega
            have hleft : pairs second first k ++ decode rest =
                pairs second first count ++ (pairs second first (k - count) ++ decode rest) := by
              calc
                _ = pairs second first (count + (k - count)) ++ decode rest :=
                  congrArg (fun j => pairs second first j ++ decode rest) hk
                _ = _ := by rw [pairs_add, List.append_assoc]
            have hright : decode right = first :: decode (pop right).2 := by
              rw [decode_pop_cons right hg.1, hg.2.1]
            simpa only [unpackConfig, unpack, decode, decode_prependBit,
              decode_prependPairs, hleft, hright] using hs
          · cases h

inductive Op where
  | one
  | right (pairs : Nat)
  | left (pairs : Nat)
  deriving DecidableEq, Repr

def perform {n : Nat} (m : Machine n) (labels : BitLabels n)
    (c : Configuration n) : Op → Option (Configuration n × Nat × List Bool)
  | .one => some ((step m labels c).1, 1, (step m labels c).2)
  | .right count => (sweepRight m labels count c).map fun out => (out, 2 * count, [])
  | .left count => (sweepLeft m labels count c).map fun out => (out, 2 * count, [])

theorem perform_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (op : Op) (c out : Configuration n) (ticks : Nat) (word : List Bool)
    (h : perform m labels c op = some (out, ticks, word)) :
    (FiniteTape.system m labels).Block (unpackConfig c) ticks (unpackConfig out) word ∧
      0 < ticks := by
  cases op with
  | one =>
    simp only [perform, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    have hs := step_sound m labels c
    have he : (FiniteTape.system m labels).step (unpackConfig c) =
        (unpackConfig (step m labels c).1, (step m labels c).2) := by
      exact Prod.ext hs.1.symm hs.2.symm
    exact ⟨WordEventSystem.Block.single _ he, by omega⟩
  | right count =>
    simp only [perform] at h
    cases hr : sweepRight m labels count c with
    | none => simp [hr] at h
    | some z =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      have hp : 0 < count := by
        unfold sweepRight at hr
        split at hr <;> simp_all
      exact ⟨sweepRight_sound m labels count c z hr, by omega⟩
  | left count =>
    simp only [perform] at h
    cases hr : sweepLeft m labels count c with
    | none => simp [hr] at h
    | some z =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      have hp : 0 < count := by
        unfold sweepLeft at hr
        split at hr <;> simp_all
      exact ⟨sweepLeft_sound m labels count c z hr, by omega⟩

def run {n : Nat} (m : Machine n) (labels : BitLabels n) :
    Configuration n → List Op → Option (Configuration n × Nat × List Bool)
  | c, [] => some (c, 0, [])
  | c, op :: ops => do
      let (middle, t, w) ← perform m labels c op
      let (finish, u, v) ← run m labels middle ops
      some (finish, t + u, w ++ v)

/-- The untrusted operation list can only produce an exact physical block;
every nonempty accepted list advances time strictly. -/
theorem run_sound {n : Nat} (m : Machine n) (labels : BitLabels n)
    (ops : List Op) (c out : Configuration n) (ticks : Nat) (word : List Bool)
    (h : run m labels c ops = some (out, ticks, word)) :
    (FiniteTape.system m labels).Block (unpackConfig c) ticks (unpackConfig out) word ∧
      (ops ≠ [] → 0 < ticks) := by
  induction ops generalizing c out ticks word with
  | nil =>
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨WordEventSystem.Block.refl _ _, by simp⟩
  | cons op ops ih =>
    cases hp : perform m labels c op with
    | none => simp [run, hp] at h
    | some value =>
      obtain ⟨middle, t, w⟩ := value
      cases hr : run m labels middle ops with
      | none => simp [run, hp, hr] at h
      | some value =>
        obtain ⟨finish, u, v⟩ := value
        simp [run, hp, hr] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        have ha := perform_sound m labels op c middle t w hp
        have hb := ih middle finish u v hr
        exact ⟨ha.1.trans _ hb.1, fun _ => by omega⟩

end PASoundness.M236.PackedTape
