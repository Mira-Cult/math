import Shared.Beeping.NPcoNP.Bootstrap284BankDecode

/-! Every prefix of the checked zero-block run can be decoded while keeping
the remaining bank and four tail bits. No mapping to graph registers is
asserted here. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BankPrefix

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode

theorem blank_start_read :
    readCells (machine.system.run 2133492).tape (-3821) 3825 =
      encode (List.replicate 1909 0 ++ [1]) ++ [true,true,true,true] := by
  have hl : (encode (List.replicate 1909 0 ++ [1]) ++
      [true,true,true,true]).length=3825 := by
    rw [encode_append,encode_single,List.length_append,List.length_append,
      zeros_length,block_length]
    decide
  have hr := read_of_holds (machine.system.run 2133492).tape (-3821)
    (encode (List.replicate 1909 0 ++ [1]) ++ [true,true,true,true]) blank_start_bank
  rw [hl] at hr
  exact hr

/-- Decode any chosen number of the initial zero blocks, preserving all
remaining blocks and the four trailing bits as an explicit suffix. -/
theorem blank_start_decodes_zero_prefix (k : Nat) (hk : k ≤ 1909) :
    decode k (readCells (machine.system.run 2133492).tape (-3821) 3825) =
      some (List.replicate k 0,
        encode (List.replicate (1909-k) 0 ++ [1]) ++ [true,true,true,true]) := by
  have hs : List.replicate 1909 0 =
      List.replicate k 0 ++ List.replicate (1909-k) 0 := by
    have hsum : k+(1909-k)=1909 := by omega
    calc
      List.replicate 1909 0 = List.replicate (k+(1909-k)) 0 :=
        congrArg (fun n : Nat => List.replicate n 0) hsum.symm
      _ = List.replicate k 0 ++ List.replicate (1909-k) 0 :=
        List.replicate_add k (1909-k) 0
  have hw : encode (List.replicate 1909 0 ++ [1]) ++ [true,true,true,true] =
      encode (List.replicate k 0) ++
        (encode (List.replicate (1909-k) 0 ++ [1]) ++ [true,true,true,true]) := by
    rw [hs,List.append_assoc,encode_append,List.append_assoc]
  rw [blank_start_read,hw]
  have hd := decode_encode (List.replicate k 0)
    (encode (List.replicate (1909-k) 0 ++ [1]) ++ [true,true,true,true])
  simpa only [List.length_replicate] using hd

end Shared.Beeping.NPcoNP.Bootstrap284BankPrefix

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BankPrefix.blank_start_decodes_zero_prefix
