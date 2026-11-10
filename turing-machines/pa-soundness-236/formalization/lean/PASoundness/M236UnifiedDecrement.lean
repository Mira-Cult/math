import PASoundness.M236DecrementRoot
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.DecrementRoot
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def reserveAfter (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat) : List Nat :=
  if registers r = 0 then reserve else reserve ++ [0]

def tailAfter (registers : RegisterMachine.Bank 9) (r : Fin 9) (tail : List Bool) : List Bool :=
  if registers r = 0 then false :: tail else tail

/-- For any register value, there is a concrete prepared full-tape execution
whose decoded bank agrees with independent `decNZ`; the residual tail and
reserve retain the literal zero/positive distinction. -/
theorem concrete_decrement (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (head : Int) (left tail : List Bool) :
    ∃ (word : List Bool) (write : Bool) (time : Nat) (endHead : Int) (padding : Nat)
      (pcTail : List Bool) (finish : Config 237),
      Preparation.NamedPath Grammar.nodes 157 word
        (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none) ∧
      0 < time ∧
      (machineWordSystem raw rawLabels).Block (Redispatch.rootConfig registers r reserve gap word head left tail) time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate padding false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++
              reserveAfter registers r reserve) ++ tailAfter registers r tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block
        (mapConfig (Redispatch.rootConfig registers r reserve gap word head left tail)) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + (reserveAfter registers r reserve).length)
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++
          reserveAfter registers r reserve) ++ tailAfter registers r tail) =
        some (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++
          reserveAfter registers r reserve, tailAfter registers r tail) ∧
      (RegisterMachine.execute (.decNZ r) registers).output = [] ∧
      ((RegisterMachine.execute (.decNZ r) registers).success = true ↔ 0 < registers r) := by
  cases h : registers r with
  | zero =>
    obtain ⟨word, write, time, endHead, scratch1, scratch2, pcTail, finish,
      hpath, ht, hp, hr, hq, hd, hout⟩ := concrete_zero registers r h reserve gap head left tail
    refine ⟨word, write, time, endHead, gap + (scratch2 + scratch1 + 3), pcTail, finish,
      hpath, ht, hp, ?_, hq, ?_, ?_, (by simpa [h] using RegisterMachine.decNZ_success_iff registers r)⟩
    · simpa [reserveAfter, tailAfter, hout, h] using hr
    · simpa [reserveAfter, tailAfter, hout, h] using hd
    · simp [hout]
  | succ value =>
    have hv : registers r = value + 1 := by simpa using h
    obtain ⟨word, write, time, endHead, scratch, pcTail, finish,
      hpath, ht, hp, hr, hq, hd, hout⟩ := concrete_positive registers r value hv reserve gap head left tail
    refine ⟨word, write, time, endHead, gap + scratch + 2, pcTail, finish,
      hpath, ht, hp, ?_, hq, ?_, ?_, (by simpa [h] using RegisterMachine.decNZ_success_iff registers r)⟩
    · simpa [reserveAfter, tailAfter, hv] using hr
    · simpa [reserveAfter, tailAfter, hv] using hd
    · simp [hout]
end PASoundness.M236.DecrementRoot
