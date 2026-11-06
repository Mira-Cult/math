import Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Explicitly supplied right-hand padding survives the literal selector cycle.
This is a finite local segment, not an assertion of blank-start reachability or
of an indefinitely repeatable cycle. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroCyclePadding
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
attribute [local irreducible] machine

/-- The shifted selector suffix has exactly the length of the original
encoded bank less its first two cells. -/
theorem bank_suffix_length (v : Nat) (rest : List Nat) :
    (bankSuffix v rest).length + 2 = (encode (v::rest)).length := by
  have hl : (rest.flatMap (fun z => false :: List.replicate (z+1) true)).length =
      (encode rest).length := by
    induction rest with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_replicate, encode, block_length] at *
      omega
  simp only [bankSuffix, List.length_append, List.length_replicate, hl, encode, block_length]
  omega

/-- If five zeros and an arbitrary finite suffix are supplied after the bank,
one new zero-valued bank entry is created while three zeros and the suffix
remain available. No unspecified tape cells are assumed blank. -/
theorem all_zero_cycle_padded (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      silentSegment machine (cfg 93 a t) (cfg 83 (a+25) final)
        (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) ∧
      Holds final (a-2) (markerWindow (List.replicate 13 0 ++ [0])) ∧
      final (a-3)=t (a-3) ∧ final (a+26)=true ∧
      Holds final (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → final q=t q) := by
  let base := a+36+(r : Int)
  let oldPrefix := encode (v::rest) ++ [false,false,false]
  have hbank : Holds t base oldPrefix :=
    holds_prefix_word t base oldPrefix ([false,false] ++ suffix) bank
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hresult,hleft,hright⟩ :=
    all_zero_positive_cycle_framed a r v rest t window left0 earlier marker nextZero h0 h1 hz hm delimiter hbank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let newPrefix := encode (v::rest) ++ [true,false,false]
  have htail : Holds t (base+((oldPrefix.length : Nat) : Int)) ([false,false] ++ suffix) :=
    holds_append_tail t base oldPrefix ([false,false] ++ suffix) bank
  have heqlen : oldPrefix.length=newPrefix.length := by simp [oldPrefix,newPrefix]
  have htail' : Holds final (base+((newPrefix.length : Nat) : Int)) ([false,false] ++ suffix) := by
    rw [← heqlen]
    apply holds_transport t final _ _ htail
    intro q hq _
    symm
    apply hright q
    · have hl := bank_suffix_length v rest
      simp only [oldPrefix, List.length_append, List.length_cons, List.length_nil] at hq
      push_cast at *
      omega
    · simp only [oldPrefix, List.length_append, List.length_cons, List.length_nil,
        encode, block_length] at hq
      push_cast at *
      omega
  have hfull := holds_append_intro final base newPrefix ([false,false] ++ suffix) hresult htail'
  have hrew : newPrefix ++ ([false,false] ++ suffix) =
      (encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix := by
    rw [append_zero_block (v::rest)]
    simp [newPrefix, List.append_assoc]
  rw [hrew] at hfull
  exact ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hfull,hleft⟩

#print axioms bank_suffix_length
#print axioms all_zero_cycle_padded
end Shared.Beeping.NPcoNP.NativeAllZeroCyclePadding
