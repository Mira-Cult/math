import Shared.Beeping.NPcoNP.NativeHalfEvenQuotient
import Shared.Beeping.NPcoNP.NativeHalfOddQuotient

/-! Shared quotient and suffix contract for both parity cases of the
prepared physical HALF loop. It does not assert graph-entry reachability
or identify the later control-branch interpretation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfPreparedCorrect

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfEvenQuotient
open Shared.Beeping.NPcoNP.NativeHalfOddQuotient
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Every prepared residual length finishes in positive finite silent time
at state 1, leaving the selected quotient block and the decoded suffix.
`m` counts right-block ones; it is not itself the original register value.
The separately appended final reserve is `10`. -/
theorem prepared_quotient_and_bank (base : Int → Bool) (b z : Int) (a m : Nat)
    (xs : List Nat) (ha : 1≤a) (hz : ∀ p≤z, base p=false)
    (hleft : ∀ p, b-(a : Int)≤p → p<b → base p=true) :
    ∃ (n₁ n₂ : Nat) (head gap : Int) (finalTape : Int → Bool),
      0<n₁ ∧ 0<n₂ ∧ sourceValue a m%2=(m+1)%2 ∧
      Holds finalTape (b-(a : Int)) (block (sourceValue a m/2)) ∧
      let values := xs ++ List.replicate (m/2+1) 0
      let word := encode values
      decode (xs.length+(m/2+1)) (readCells finalTape (gap+2) word.length)=some (values,[]) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 1 head finalTape) (n₁+n₂) := by
  have hpar : sourceValue a m%2=(m+1)%2 := by simp only [sourceValue]; omega
  by_cases he : m%2=0
  · obtain ⟨n₁,n₂,head,gap,t,hn₁,hn₂,_,hquot,hdec,hr0,hr1,hseg⟩ :=
      prepared_even_quotient_and_bank base b z a m xs ha he hz hleft
    exact ⟨n₁,n₂,head,gap,t,hn₁,hn₂,hpar,hquot,hdec,hr0,hr1,hseg⟩
  · have ho : m%2=1 := by omega
    have hcount : (m+1)/2=m/2+1 := by omega
    obtain ⟨n₁,n₂,head,gap,t,hn₁,hn₂,_,hquot,hdec,hr0,hr1,hseg⟩ :=
      prepared_odd_quotient_and_bank base b z a m xs ha ho hz hleft
    rw [hcount] at hdec hr0 hr1
    exact ⟨n₁,n₂,head-(n₂ : Int),gap,t,hn₁,hn₂,hpar,hquot,hdec,hr0,hr1,hseg⟩

end Shared.Beeping.NPcoNP.NativeHalfPreparedCorrect

#print axioms Shared.Beeping.NPcoNP.NativeHalfPreparedCorrect.prepared_quotient_and_bank
