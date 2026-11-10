import PASoundness.M236SelectorReturn

/-! Composition of named physical selection, increment, filled-gap cleanup,
and the already verified finite return counter. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.SelectorRoot
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift
open PASoundness.M236.UnaryAnchor

/-- A prepared named increment entry reaches the literal root state, with the
updated bank and reserve on the full tape. The finite control prefix and
complete entry-tape relation remain explicit assumptions. -/
theorem physical_named_increment_root
    (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (gap scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (pcTail : List Bool)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hprefix : counterPush runs [] = true :: bit :: pcTail)
    (hrel : Related
      ⟨Selector.entryState r, head,
        ⟨List.replicate scratch true ++ false ::
            (counterWord runs ++ List.replicate 6 false ++ false :: left),
          true :: false :: (bank (gap :: UnaryIncrementNine.before registers r) ++
            (List.replicate (registers r + 1) true ++ false ::
              (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)))⟩⟩ c) :
    ∃ (first : Nat) (values : List Nat) (finish : Config 237),
      (UnaryIncrementNine.after registers r ++ reserve).reverse ++
        (registers r + 1) :: (gap :: UnaryIncrementNine.before registers r).reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (shiftTime (gap :: UnaryIncrementNine.before registers r) + 2 +
          (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
            (first + 1 + (shiftTime values + 2))) + (3 * scratch + 2 * gap + 9) +
          (counterTime runs + 6) + 10) finish [] ∧
      Related
        ⟨79, head + 2 + (shiftTime (gap :: UnaryIncrementNine.before registers r) : Int) +
          ((registers r + 2 : Nat) : Int) + (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
          ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1 -
          (counterTime runs : Int) - 6 + 10,
          ⟨false :: true :: true :: (List.replicate 7 false ++ left),
            pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
              (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (shiftTime (gap :: UnaryIncrementNine.before registers r) + 2 +
          (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
            (first + 1 + (shiftTime values + 2))) + (3 * scratch + 2 * gap + 9) +
          (counterTime runs + 6) + 10) (mapConfig finish) [] ∧
      0 < shiftTime (gap :: UnaryIncrementNine.before registers r) + 2 +
          (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
            (first + 1 + (shiftTime values + 2))) + (3 * scratch + 2 * gap + 9) +
          (counterTime runs + 6) + 10 ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  let suffix := List.replicate (gap + scratch + 2) false ++ true :: false ::
    (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail)
  obtain ⟨first, values, _, _, middle, he, _, _, hp, hr, hq, ht, hd⟩ :=
    SelectorReturn.physical_named_increment registers r reserve gap scratch head
      (counterWord runs ++ List.replicate 6 false ++ false :: left) tail c hrel
  let h64 := head + 2 + (shiftTime (gap :: UnaryIncrementNine.before registers r) : Int) +
    ((registers r + 2 : Nat) : Int) + (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
    ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1
  obtain ⟨endCounter, hpc, hrc, hqc, _⟩ := physical_counter runs h64 (false :: left) suffix middle hr
  have hroot : counterPush runs suffix = true :: bit :: (pcTail ++ suffix) := by
    have h := counterPush_append runs [] suffix
    simpa [hprefix] using h
  rw [hroot] at hrc
  let h65 := h64 - (counterTime runs : Int) - 6
  have hrootRel : Related ⟨65, h65,
      ⟨left, List.replicate 7 false ++ true :: true :: bit :: (pcTail ++ suffix)⟩⟩ endCounter := by
    simpa [h65, moveLeft, List.replicate_succ] using hrc
  have hb := root_reentry 7 bit h65 left (pcTail ++ suffix)
  obtain ⟨finish, hpr, hrr⟩ := BulkSweep.physical_block raw rawLabels _ _ endCounter 10 hrootRel hb
  have hqr := BootstrapScan.mapped_block hpr
  refine ⟨first, values, finish, he, ?_, ?_, ?_, by omega, hd⟩
  · simpa using (hp.trans (machineWordSystem raw rawLabels) hpc).trans (machineWordSystem raw rawLabels) hpr
  · simpa [h65, h64, suffix, Int.add_assoc] using hrr
  · simpa using (hq.trans (machineWordSystem machine machineLabels) hqc).trans
      (machineWordSystem machine machineLabels) hqr

end PASoundness.M236.SelectorRoot
