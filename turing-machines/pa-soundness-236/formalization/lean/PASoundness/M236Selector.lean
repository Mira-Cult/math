import PASoundness.M236MetadataIntegration
import PASoundness.M236UnaryAnchor

/-! The literal named increment entries and their unary selection rows. The
prepared marker/gap layout is explicit; no blank-start admission is asserted. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Selector
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift
open PASoundness.M236.Metadata PASoundness.M236.TextEncoding

def registerNames : Vector String 9 := #v[
  "scratch.copy", "k.stage", "k.rest", "k.count", "k.top", "k.env", "k.a", "k.b", "k.c"]

def entryStates : Vector (Fin 237) 9 := #v[58, 54, 52, 48, 56, 50, 42, 44, 46]

def entryState (r : Fin 9) : Fin 237 := entryStates[r]

def scanState (k : Fin 10) : Fin 237 :=
  if k.val = 0 then 7 else ⟨9 + 2 * k.val, by have h := k.isLt; omega⟩

def nextState (k : Fin 10) : Fin 237 :=
  if h : k.val = 0 then 9 else scanState ⟨k.val - 1, by have hk := k.isLt; omega⟩

def entryIndex (r : Fin 9) : Fin 10 := ⟨r.val + 1, by have h := r.isLt; omega⟩

/-- The retained metadata's register-order field exactly lists these nine names. -/
theorem register_order_field : part4 = bytes
    ("\n  },\n  \"register_order\": [\n" ++
      String.intercalate ",\n" (registerNames.toList.map (fun name => "    " ++ quote name)) ++
      "\n  ],\n") := by decide

/-- Each selected physical entry is the metadata state named for that register. -/
theorem entry_names : ∀ r : Fin 9,
    stateNames[entryState r] = "3." ++ registerNames[r] ++ ".inc" := by decide

/-- The prepared-one branch and its event are the literal rows. -/
theorem entry_rows : ∀ r : Fin 9,
    raw.table.row (entryState r) true = ⟨false, .right, scanState (entryIndex r), false⟩ ∧
      rawLabels.at (entryState r) true = none := by decide

/-- The zero branch enters preparation, rather than the ready selector. -/
theorem unprepared_rows : ∀ r : Fin 9,
    raw.table.row (entryState r) false = ⟨true, .right, 4, false⟩ ∧
      rawLabels.at (entryState r) false = none := by decide

/-- Every selector scan preserves ones and advances one state on its zero. -/
theorem scan_rows : ∀ k : Fin 10,
    raw.table.row (scanState k) true = ⟨true, .right, scanState k, false⟩ ∧
    raw.table.row (scanState k) false = ⟨false, .right, nextState k, false⟩ ∧
    rawLabels.at (scanState k) true = none ∧ rawLabels.at (scanState k) false = none := by decide

private theorem replicate_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ (true :: tail) = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- Any selector state scans an arbitrary finite run of ones unchanged. -/
theorem scan_ones (k : Fin 10) (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨scanState k, head, ⟨left, List.replicate count true ++ false :: tail⟩⟩ count
      ⟨scanState k, head + (count : Int), ⟨List.replicate count true ++ left, false :: tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨scanState k, head, ⟨left, false :: tail⟩⟩
  | succ count ih =>
    have hr := scan_rows k
    have hs : rawSystem.step
        ⟨scanState k, head, ⟨left, List.replicate (count + 1) true ++ false :: tail⟩⟩ =
        (⟨scanState k, head + 1, ⟨true :: left, List.replicate count true ++ false :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hr.1, hr.2.2.1,
        Move.apply, moveRight, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem (ih (head + 1) (true :: left))
    have hh : head + 1 + (count : Int) = head + ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

/-- Crossing the following zero advances the selector without modifying the tape. -/
theorem scan_stop (k : Fin 10) (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨scanState k, head, ⟨left, List.replicate count true ++ false :: tail⟩⟩
      (count + 1)
      ⟨nextState k, head + ((count + 1 : Nat) : Int),
        ⟨false :: (List.replicate count true ++ left), tail⟩⟩ [] := by
  have hb := scan_ones k count head left tail
  have hr := scan_rows k
  have hs : rawSystem.step ⟨scanState k, head + (count : Int),
      ⟨List.replicate count true ++ left, false :: tail⟩⟩ =
      (⟨nextState k, head + (count : Int) + 1,
        ⟨false :: (List.replicate count true ++ left), tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hr.2.1, hr.2.2.2,
      Move.apply, moveRight]
  have hh : head + (count : Int) + 1 = head + ((count + 1 : Nat) : Int) := by omega
  simpa only [List.nil_append, hh] using hb.trans rawSystem (WordEventSystem.Block.single rawSystem hs)

private theorem next_zero : nextState ⟨0, by decide⟩ = 9 := by decide

private theorem next_succ (k : Nat) (hk : k < 9) :
    nextState ⟨k + 1, by omega⟩ = scanState ⟨k, by omega⟩ := by
  simp [nextState]

/-- Starting at the selector corresponding to a nonempty finite bank,
scan every block and reach state 9 at the next cell. The bank is unchanged. -/
theorem scan_bank (values : List Nat) (hne : values ≠ []) (hsize : values.length ≤ 10)
    (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨scanState ⟨values.length - 1, by simp at hne; omega⟩, head,
        ⟨left, bank values ++ tail⟩⟩
      (shiftTime values)
      ⟨9, head + (shiftTime values : Int), ⟨(bank values).reverse ++ left, tail⟩⟩ [] := by
  induction values generalizing head left with
  | nil => contradiction
  | cons value rest ih =>
    cases rest with
    | nil =>
      have hb := scan_stop ⟨0, by decide⟩ (value + 1) head left tail
      have ht : value + 1 + 1 = value + 2 := by omega
      have hh : head + ((value + 1 + 1 : Nat) : Int) = head + ((value + 2 : Nat) : Int) := by omega
      rw [next_zero, ht, hh] at hb
      simpa [bank, shiftTime, List.replicate_succ, List.reverse_cons,
        List.reverse_append, List.reverse_replicate, List.append_assoc, replicate_shift] using hb
    | cons next rest =>
      have hk : (next :: rest).length - 1 < 9 := by simp only [List.length_cons] at hsize ⊢; omega
      have hfirst := scan_stop ⟨(next :: rest).length, by simp at hsize; omega⟩ (value + 1) head left
        (bank (next :: rest) ++ tail)
      have hn : nextState ⟨(next :: rest).length, by simp at hsize; omega⟩ =
          scanState ⟨(next :: rest).length - 1, by simp at hsize; omega⟩ := by
        have hn' := next_succ ((next :: rest).length - 1) hk
        simpa using hn'
      rw [hn] at hfirst
      have hrest := ih (by simp) (by simp at hsize ⊢; omega)
        (head + ((value + 2 : Nat) : Int)) (false :: (List.replicate (value + 1) true ++ left))
      have hb := hfirst.trans rawSystem hrest
      have ht : value + 1 + 1 + shiftTime (next :: rest) = value + 2 + shiftTime (next :: rest) := by omega
      have hh : head + ((value + 2 : Nat) : Int) + (shiftTime (next :: rest) : Int) =
          head + ((value + 2 + shiftTime (next :: rest) : Nat) : Int) := by omega
      rw [ht, hh] at hb
      simpa only [bank, shiftTime, List.length_cons, Nat.add_sub_cancel, List.cons_append,
        List.nil_append, List.reverse_cons, List.reverse_append, List.reverse_replicate,
        List.append_assoc, List.replicate_succ, replicate_shift] using hb

private theorem entry_next : ∀ r : Fin 9,
    nextState (entryIndex r) = scanState ⟨r.val, by have h := r.isLt; omega⟩ := by decide

/-- From a prepared named increment entry, cross the fixed separator, the
filled gap-plus-anchor run and the preceding register blocks. The selected
register begins under the head in raw state 9; all traversed bank bits are
preserved and the prepared marker is cleared. -/
theorem entry_block (r : Fin 9) (gap : Nat) (before : List Nat)
    (hlen : before.length = r.val) (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨entryState r, head, ⟨left, true :: false :: (bank (gap :: before) ++ tail)⟩⟩
      (shiftTime (gap :: before) + 2)
      ⟨9, head + 2 + (shiftTime (gap :: before) : Int),
        ⟨(bank (gap :: before)).reverse ++ false :: false :: left, tail⟩⟩ [] := by
  have hr := entry_rows r
  have hs : rawSystem.step ⟨entryState r, head,
      ⟨left, true :: false :: (bank (gap :: before) ++ tail)⟩⟩ =
      (⟨scanState (entryIndex r), head + 1,
        ⟨false :: left, false :: (bank (gap :: before) ++ tail)⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hr.1, hr.2,
      Move.apply, moveRight]
  have hsep := scan_stop (entryIndex r) 0 (head + 1) (false :: left) (bank (gap :: before) ++ tail)
  rw [entry_next] at hsep
  have hsize : (gap :: before).length ≤ 10 := by simp [hlen]
  have hsep' : rawSystem.Block
      ⟨scanState (entryIndex r), head + 1, ⟨false :: left, false :: (bank (gap :: before) ++ tail)⟩⟩ 1
      ⟨scanState ⟨r.val, by have h := r.isLt; omega⟩, head + 2,
        ⟨false :: false :: left, bank (gap :: before) ++ tail⟩⟩ [] := by
    simpa [Int.add_assoc] using hsep
  have hbank := scan_bank (gap :: before) (by simp) hsize (head + 2) (false :: false :: left) tail
  have hidx : scanState ⟨(gap :: before).length - 1, by simp; have := r.isLt; omega⟩ =
      scanState ⟨r.val, by have := r.isLt; omega⟩ := by
    congr 1
    apply Fin.ext
    simp [hlen]
  rw [hidx] at hbank
  have hb := ((WordEventSystem.Block.single rawSystem hs).trans rawSystem hsep').trans rawSystem hbank
  have ht : 1 + 1 + shiftTime (gap :: before) = shiftTime (gap :: before) + 2 := by omega
  simpa only [List.nil_append, ht] using hb

/-- The named-entry selection block refines the complete raw and quotient
two-way tapes with identical positive time and no events. -/
theorem physical_entry (r : Fin 9) (gap : Nat) (before : List Nat)
    (hlen : before.length = r.val) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨entryState r, head, ⟨left, true :: false :: (bank (gap :: before) ++ tail)⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (shiftTime (gap :: before) + 2) finish [] ∧
      Related ⟨9, head + 2 + (shiftTime (gap :: before) : Int),
        ⟨(bank (gap :: before)).reverse ++ false :: false :: left, tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (shiftTime (gap :: before) + 2)
        (mapConfig finish) [] ∧ 0 < shiftTime (gap :: before) + 2 := by
  have hb := entry_block r gap before hlen head left tail
  obtain ⟨finish, hp, hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨finish, hp, hr, BootstrapScan.mapped_block hp, by omega⟩

theorem before_length (registers : RegisterMachine.Bank 9) (r : Fin 9) :
    (UnaryIncrementNine.before registers r).length = r.val := by
  simp [UnaryIncrementNine.before, UnaryNine.values_length, Nat.min_eq_left (Nat.le_of_lt r.isLt)]

/-- The exact register-order field and state-name map from the bound metadata
agree with the independent nine-register indexing. -/
theorem named_order (r : Fin 9) :
    stateNames[entryState r] = "3." ++ registerNames[r] ++ ".inc" ∧
    part4 = bytes ("\n  },\n  \"register_order\": [\n" ++
      String.intercalate ",\n" (registerNames.toList.map (fun name => "    " ++ quote name)) ++
      "\n  ],\n") := ⟨entry_names r, register_order_field⟩

end PASoundness.M236.Selector
