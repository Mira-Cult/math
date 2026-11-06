import Shared.Beeping.NPcoNP.NativeHalfEvenBank
import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
import Shared.Beeping.NPcoNP.Bootstrap284BankDecode

/-! Prepared even-residual HALF return, quotient block and decoded suffix.
The supplied left block and zero tail are hypotheses; graph-entry and
blank-start reachability remain separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEvenQuotient

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfEvenBank
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- In the loop arithmetic, an even residual gives an odd source value;
the quotient's unary block contains `a+m/2` ones. -/
theorem even_residual_quotient_length (a m : Nat) (ha : 1≤a) (he : m%2=0) :
    sourceValue a m % 2=1 ∧ sourceValue a m / 2+1=a+m/2 := by
  simp only [sourceValue]
  omega

/-- The selected quotient block in an even-branch bank layout. -/
theorem quotient_block (base outBase : Int → Bool) (b gap : Int) (a m : Nat)
    (word : List Bool) (ha : 1≤a) (he : m%2=0)
    (hgap : gap=b+((m/2 : Nat) : Int)-1)
    (hleft : ∀ p, b-(a : Int)≤p → p<b → base p=true)
    (hprefix : ∀ p<b, outBase p=base p)
    (hfilled : ∀ p, b≤p → p≤gap → outBase p=true) :
    Holds (after outBase (gap+1) word) (b-(a : Int)) (block (sourceValue a m/2)) := by
  let start := b-(a : Int)
  let count := a+m/2
  let t := after outBase (gap+1) word
  have hcount : sourceValue a m/2+1=count := (even_residual_quotient_length a m ha he).2
  have hend : start+(count : Int)=gap+1 := by dsimp [start,count] at *; omega
  have hones : Holds t start (List.replicate count true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<count := by simpa using hi
    have hhi : start+(i : Int)≤gap := by omega
    change after outBase (gap+1) word (start+(i : Int)) = _
    rw [after_prefix _ _ _ _ (by omega)]
    by_cases hb : start+(i : Int)<b
    · rw [hprefix _ hb,hleft _ (by dsimp [start]; omega) hb]
      simp
    · rw [hfilled _ (by omega) hhi]
      simp
  have hsep : Holds t (start+count) [false] := by
    change t (start+(count : Int))=false ∧ True
    rw [hend]
    exact ⟨(gap_cells outBase (gap+1) word).2.2,trivial⟩
  have hsep' : Holds t (start+((List.replicate count true).length : Int)) [false] := by
    simpa using hsep
  have hh := holds_append t start (List.replicate count true) [false] hones hsep'
  change Holds t start (block (sourceValue a m/2))
  simpa [block,hcount] using hh

/-- For every supplied even residual and nonempty left block, the literal
table returns silently to state 1. The selected quotient is encoded on tape,
the original suffix decodes unchanged followed by `m/2+1` zero blocks,
and the separate `10` reserve is retained. -/
theorem prepared_even_quotient_and_bank (base : Int → Bool) (b z : Int) (a m : Nat)
    (xs : List Nat) (ha : 1≤a) (he : m%2=0)
    (hz : ∀ p≤z, base p=false)
    (hleft : ∀ p, b-(a : Int)≤p → p<b → base p=true) :
    ∃ (n₁ n₂ : Nat) (head gap : Int) (finalTape : Int → Bool),
      0<n₁ ∧ 0<n₂ ∧ sourceValue a m%2=1 ∧
      Holds finalTape (b-(a : Int)) (block (sourceValue a m/2)) ∧
      let values := xs ++ List.replicate (m/2+1) 0
      let word := encode values
      decode (xs.length+(m/2+1)) (readCells finalTape (gap+2) word.length)=some (values,[]) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 1 head finalTape) (n₁+n₂) := by
  obtain ⟨n₁,gap,outBase,hn₁,hgap,hprefix,hfilled,hfirst⟩ :=
    prepared_even_to23_bank base b m xs he
  let values := xs ++ List.replicate (m/2+1) 0
  let word := encode values
  let t := after outBase (gap+1) word
  let left := min z (b-1)
  let k := (gap-min left gap).toNat
  have hk : gap-(k : Int)≤left := by
    have hn : 0≤gap-min left gap := by omega
    have hh : (k : Int)=gap-min left gap := Int.toNat_of_nonneg hn
    omega
  have ht : ∀ p≤gap-(k : Int), t p=false := by
    intro p hp
    have hza : left≤z := min_le_left _ _
    have hba : left≤b-1 := min_le_right _ _
    have hb : p<b := by omega
    have hg : p<gap+1 := by omega
    change after outBase (gap+1) word p=false
    rw [after_prefix _ _ _ _ hg,hprefix _ hb]
    exact hz _ (by omega)
  obtain ⟨n₂,head,hn₂,_,hsecond⟩ := scan_left_zero k gap t ht false
  have hquot : Holds t (b-(a : Int)) (block (sourceValue a m/2)) :=
    quotient_block base outBase b gap a m word ha he hgap hleft hprefix hfilled
  have hbits : ∀ i : Nat, i<word.length → t (gap+2+(i : Int))=bitAt word i := by
    intro i hi
    have hh := after_suffix_bit outBase (gap+1) word i hi
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using hh
  have hreserve0 : t (gap+2+(word.length : Int))=true := by
    have hh := (appended_zero_block outBase (gap+1) word).1
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using hh
  have hreserve1 : t (gap+3+(word.length : Int))=false := by
    have hh := (appended_zero_block outBase (gap+1) word).2
    simpa only [Int.add_assoc,show (1 : Int)+2=3 by decide] using hh
  have hh : Holds t (gap+2) word := by
    apply holds_of_get
    intro i hi
    have hv := hbits i hi
    simpa only [bitAt,List.getElem?_eq_getElem hi,Option.getD_some] using hv
  have hr := read_of_holds t (gap+2) word hh
  have hd : decode (xs.length+(m/2+1)) word=some (values,[]) := by
    have hh := decode_encode values []
    simpa only [List.append_nil,values,List.length_append,List.length_replicate] using hh
  refine ⟨n₁,n₂,head,gap,t,hn₁,hn₂,(even_residual_quotient_length a m ha he).1,
    hquot,?_,hreserve0,hreserve1,?_⟩
  · rw [hr]
    exact hd
  · exact segAdd machine _ _ _ n₁ n₂ hfirst hsecond

end Shared.Beeping.NPcoNP.NativeHalfEvenQuotient

#print axioms Shared.Beeping.NPcoNP.NativeHalfEvenQuotient.prepared_even_quotient_and_bank
