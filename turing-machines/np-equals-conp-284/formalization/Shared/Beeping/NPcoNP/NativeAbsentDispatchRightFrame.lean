import Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
import Shared.Beeping.NPcoNP.NativeAbsentPositiveRightFrame
import Shared.Beeping.NPcoNP.NativeAllZeroUnitPositive
import Shared.Beeping.NPcoNP.NativeHalfSelectorExact
import Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

/-! The next scan encounters two adjacent zeros, so it is a scan of fourteen
physical delimiters, not a fourteen-value unary selector window. -/
namespace Shared.Beeping.NPcoNP.NativeAbsentDispatchRightFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeAllZeroUnitPositive
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
open Shared.Beeping.NPcoNP.NativeAbsentPositiveRightFrame
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

theorem padded_absent_positive_dispatch_with_right_frame (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a zeroWord)
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (a+36+(r : Int))
        ((encode (v::(rest ++ [0,0])) ++ [false]) ++ suffix) ∧
      out (a+24)=true ∧ out (a+35+(r : Int))=false ∧
      (∀ q, a+24<q → q<a+34+(r : Int) → out q=false) ∧
      out (a+34+(r : Int))=true ∧
      (∀ q, q<a+24 → out q=t q) ∧
      (∀ q, a+36+(r : Int)+(((encode (v::rest) ++ [false,false,false]) ++ [false,false]).length : Int)≤q → out q=t q) ∧
      (t (a-4)=true → silentSegment machine (cfg 93 a t) (cfg 93 (a-3) out) (n+28)) ∧
      (t (a-4)=false → silentSegment machine (cfg 93 a t) (cfg 93 a out) (n+31)) := by
  obtain ⟨n,out,hn,hseg,hmark,hblank,hcorr,hstop,hbank,hframe,hframeRight⟩ :=
    padded_absent_next_positive_with_right_frame a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  have hbank' := positive_bank_extended_with_suffix (a+36+(r : Int)) v rest suffix out hbank
  obtain ⟨hleft,hright⟩ := positive_return_dispatch a t out window left0 earlier absent hframe
  refine ⟨n,out,hn,hbank',hmark,hblank,hcorr,hstop,hframe,hframeRight,?_,?_⟩
  · intro h
    exact segAdd machine _ _ _ n 28 hseg (hleft h)
  · intro h
    exact segAdd machine _ _ _ n 31 hseg (hright h)


#print axioms padded_absent_positive_dispatch_with_right_frame
end Shared.Beeping.NPcoNP.NativeAbsentDispatchRightFrame
