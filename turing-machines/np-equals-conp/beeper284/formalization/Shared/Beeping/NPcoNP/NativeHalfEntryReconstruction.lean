import Shared.Beeping.NPcoNP.NativeHalfEntryZero
import Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
import Shared.Beeping.NPcoNP.NativeHalfBankFirst

/-! Recover the canonical native-half entry tape from an exact finite
physical suffix and a blank right tail. The reserve is an explicit hypothesis. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryReconstruction
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfEntryZero
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfCleanupScan
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- An exact suffix, its `10` reserve, and the blank right tail determine
the whole `after` tape, with the original tape used for its protected prefix. -/
theorem after_eq_of_word (t : Int → Bool) (b : Int) (s : List Bool)
    (zero : t b=false) (word : Holds t (b+1) (s++[true,false]))
    (tail : ∀ q, b+2+((s.length : Nat):Int)≤q → t q=false) :
    after t b s=t := by
  have hbits : ∀ i : Nat, i<s.length → t (b+1+(i : Int))=bitAt s i := by
    intro i hi
    have hi' : i<(s++[true,false]).length := by simp; omega
    have hg := holds_get t (b+1) (s++[true,false]) word i hi'
    rw [List.getElem_append_left hi] at hg
    simpa [bitAt,List.getElem?_eq_getElem hi] using hg
  have hmark : t (b+1+((s.length : Nat):Int))=true := by
    have hh := holds_append_tail t (b+1) s [true,false] word
    simpa [Holds,Int.add_assoc] using hh.1
  funext q
  by_cases hleft : q<b
  · simp [after,hleft]
  · by_cases he : q=b
    · subst q
      simp [after,zero]
    · by_cases hin : q<b+1+((s.length : Nat):Int)
      · let i := (q-(b+1)).toNat
        have hi : (i : Int)=q-(b+1) := Int.toNat_of_nonneg (by omega)
        have hi' : i<s.length := by omega
        have eq : b+1+(i : Int)=q := by omega
        have hh := hbits i hi'
        rw [eq] at hh
        have heq : (q-b-1).toNat=i := by congr 1 <;> omega
        simp [after,hleft,he,hin,heq,hh]
      · by_cases hm : q=b+1+((s.length : Nat):Int)
        · subst q
          simp [after,show ¬ b+1+((s.length : Nat):Int)<b by omega,
            show b+1+((s.length : Nat):Int)≠b by omega,hmark]
        · have ht : t q=false := tail q (by omega)
          simp [after,hleft,he,hin,hm,ht]

/-- Positive-entry tape reconstruction. The leading selected cell is one;
the rest of the exact block and the `10` reserve are supplied as a word. -/
theorem entryTape_eq_of_word (t : Int → Bool) (b z : Int) (m : Nat) (xs : List Nat)
    (head : t b=true) (left : t (b-1)=true) (hz : ∀ q, q≤z → t q=false) (hzb : z<b)
    (word : Holds t (b+1) ((List.replicate m true ++ false::encode xs) ++ [true,false]))
    (tail : ∀ q, b+2+(((List.replicate m true ++ false::encode xs).length : Nat):Int)≤q → t q=false) :
    entryTape (NativeHalfState16Progress.clearAt b t) b m xs=t ∧
      (NativeHalfState16Progress.clearAt b t) (b-1)=true ∧
      (∀ q, q≤z → (NativeHalfState16Progress.clearAt b t) q=false) := by
  let base := NativeHalfState16Progress.clearAt b t
  let s := List.replicate m true ++ false::encode xs
  have hz0 : base b=false := by simp [base,NativeHalfState16Progress.clearAt]
  have hw : Holds base (b+1) (s++[true,false]) := by
    apply NativeHalfScannerFrames.holds_transport t base _ _ word
    intro q hq _
    simp [base,NativeHalfState16Progress.clearAt,show q≠b by omega]
  have ht : ∀ q, b+2+((s.length : Nat):Int)≤q → base q=false := by
    intro q hq
    have hh := tail q hq
    simpa [base,NativeHalfState16Progress.clearAt,show q≠b by omega] using hh
  have ha := after_eq_of_word base b s hz0 hw ht
  have hp : NativeHalfAllResiduals.prepared base b m xs=base := by
    rw [NativeHalfAllResiduals.prepared_shape]
    exact ha
  have he : entryTape base b m xs=t := by
    rw [entryTape,hp]
    funext q
    by_cases hq : q=b
    · subst q; simp [put,head]
    · simp [put,base,NativeHalfState16Progress.clearAt,hq]
  refine ⟨he,?_,?_⟩
  · simpa [base,NativeHalfState16Progress.clearAt] using left
  · intro q hq
    have hh := hz q hq
    simpa [base,NativeHalfState16Progress.clearAt,show q≠b by omega] using hh

/-- The existing positive quotient proof applies directly to a physical tape
with the explicit finite suffix, reserve and blank-tail interface. -/
theorem positive_quotient_of_word (t : Int → Bool) (b z : Int) (m : Nat) (xs : List Nat)
    (head : t b=true) (left : t (b-1)=true) (hz : ∀ q, q≤z → t q=false) (hzb : z<b)
    (word : Holds t (b+1) ((List.replicate m true ++ false::encode xs) ++ [true,false]))
    (tail : ∀ q, b+2+(((List.replicate m true ++ false::encode xs).length : Nat):Int)≤q → t q=false) :
    ∃ (n : Nat) (headPos gap : Int) (out : Int → Bool), 0<n ∧
      Holds out (b-1) (block ((m+1)/2)) ∧
      let values := xs ++ List.replicate (m/2+1) 0
      let encoded := encode values
      decode (xs.length+(m/2+1)) (readCells out (gap+2) encoded.length)=some (values,[]) ∧
      out (gap+2+(encoded.length : Int))=true ∧ out (gap+3+(encoded.length : Int))=false ∧
      silentSegment machine (cfg 29 (b-1) t) (cfg 1 headPos out) n := by
  dsimp only
  let base := NativeHalfState16Progress.clearAt b t
  obtain ⟨he,hl,hblank⟩ := entryTape_eq_of_word t b z m xs head left hz hzb word tail
  obtain ⟨n,headPos,gap,out,hn,hquot,hdecode,hreserve,hzero,hseg⟩ :=
    entry_nonzero_quotient_and_bank base b z m xs hl hblank
  rw [he] at hseg
  exact ⟨n,headPos,gap,out,hn,hquot,hdecode,hreserve,hzero,hseg⟩

/-- The zero quotient proof also applies directly to a supplied physical
tape with an exact encoded suffix and the explicit `10` reserve. -/
theorem zero_quotient_of_word (t : Int → Bool) (b z : Int) (xs : List Nat)
    (zero : t b=false) (left : t (b-1)=true) (hz : ∀ q, q≤z → t q=false)
    (word : Holds t (b+1) (encode xs ++ [true,false]))
    (tail : ∀ q, b+2+(((encode xs).length : Nat):Int)≤q → t q=false) :
    ∃ (n₁ n₂ : Nat) (headPos : Int) (out : Int → Bool), 0<n₁ ∧ 0<n₂ ∧
      Holds out (b-1) (block 0) ∧
      decode xs.length (readCells out (b+1) (encode xs).length)=some (xs,[]) ∧
      out (b+1+((encode xs).length : Int))=true ∧
      out (b+2+((encode xs).length : Int))=false ∧
      silentSegment machine (cfg 29 (b-1) t) (cfg 1 headPos out) (2+n₁+n₂) := by
  have he := after_eq_of_word t b (encode xs) zero word tail
  obtain ⟨n₁,n₂,headPos,out,h1,h2,hblock,hdecode,hmark,hzero,hseg⟩ :=
    entry_zero_quotient_and_bank t b z xs left hz
  rw [he] at hseg
  exact ⟨n₁,n₂,headPos,out,h1,h2,hblock,hdecode,hmark,hzero,hseg⟩

#print axioms positive_quotient_of_word
#print axioms zero_quotient_of_word
#print axioms after_eq_of_word
#print axioms entryTape_eq_of_word
end Shared.Beeping.NPcoNP.NativeHalfEntryReconstruction
