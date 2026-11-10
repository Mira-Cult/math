import PASoundness.M236BootstrapCertificate
import PASoundness.M236FastTable

/-! Bind the packed runtime checker to the certified literal blank start. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PASoundness.M236.RuntimeBase

open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.BulkSweep
open PASoundness.M236.PackedTape PASoundness.M236.FastBootstrap
open PASoundness.M236.FastBootstrap.Certificate

theorem pairs_replicate (a b : Bool) (n : Nat) :
    pairs a b n = (List.replicate n [a, b]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairs, List.replicate_succ, ih]

def start : PackedTape.Configuration 237 :=
  ⟨58, -2, ⟨[.pair true false 1909, .bit true],
    [.bit true, .bit false, .bit true, .bit true, .bit true, .bit true]⟩⟩

/-- This equality carries the full, blank-background tape across the
representation change; it is not a preloaded-entry assumption. -/
theorem start_unpacked : unpackConfig start = bootState77 := by
  change unpackConfig start = ⟨58, -2, bootState77.tape⟩
  rw [exit_tape_checked]
  simp [start, unpackConfig, unpack, decode, pairs_replicate, exitTape]

theorem segment_sound (ops : List PackedTape.Op) (begin finish : PackedTape.Configuration 237)
    (ticks : Nat) (word : List Bool)
    (h : PackedFast.run FastTable.table begin ops = some (finish, ticks, word)) :
    rawSystem.Block (unpackConfig begin) ticks (unpackConfig finish) word ∧
      (ops ≠ [] → 0 < ticks) := by
  rw [FastTable.table_correct, PackedFast.run_ordinary] at h
  exact PackedTape.run_sound raw rawLabels ops begin finish ticks word h

theorem checked_block (ops : List PackedTape.Op) (finish : PackedTape.Configuration 237)
    (ticks : Nat) (word : List Bool)
    (h : PackedFast.run FastTable.table start ops = some (finish, ticks, word)) :
    rawSystem.Block rawSystem.initial (2133492 + ticks) (unpackConfig finish) word ∧
      (ops ≠ [] → 0 < ticks) := by
  have hr := segment_sound ops start finish ticks word h
  rw [start_unpacked] at hr
  have hb := bootstrap_block.trans rawSystem hr.1
  exact ⟨by simpa using hb, hr.2⟩

/-- An accepted packed program starts at the literal blank tape and preserves
the exact event prefix of both raw and quotient machines. -/
theorem blank_runtime_sound (ops : List PackedTape.Op) (finish : PackedTape.Configuration 237)
    (ticks : Nat) (word : List Bool)
    (h : PackedFast.run FastTable.table start ops = some (finish, ticks, word)) :
    Related (unpackConfig finish) ((machineWordSystem raw rawLabels).run (2133492 + ticks)) ∧
      (machineWordSystem raw rawLabels).prefixWord (2133492 + ticks) = word ∧
      (machineWordSystem machine machineLabels).prefixWord (2133492 + ticks) = word := by
  have hb := (checked_block ops finish ticks word h).1
  have hr := raw_run_sound (2133492 + ticks)
  change Related (rawSystem.advance rawSystem.initial (2133492 + ticks)) _ ∧
    rawSystem.wordFrom rawSystem.initial (2133492 + ticks) = _ at hr
  rw [hb.endpoint, hb.output] at hr
  exact ⟨hr.1, hr.2.symm, by rw [← prefix_eq]; exact hr.2.symm⟩

end PASoundness.M236.RuntimeBase
