import Shared.Beeping.NPcoNP.NativeAllZeroUnitPositive
import Shared.Beeping.NPcoNP.NativeHalfSelectorExact
import Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

/-! The next scan encounters two adjacent zeros, so it is a scan of fourteen
physical delimiters, not a fourteen-value unary selector window. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
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
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

def scanWord : List Bool := [false,false,true] ++ zeroWord.take 24
def scanCounts : List Nat := List.replicate 13 1 ++ [0]

theorem scan_word_reverse : scanWord.reverse=blocks scanCounts := by decide
theorem scan_word_length : scanWord.length=27 := by decide

/-- The returned head sees twelve original blocks, one preserved block and
an adjacent zero; the complete 14-row left scan takes 27 silent steps. -/
theorem positive_return_to92_with_prefix (a : Int) (initial out : Int → Bool)
    (hpre : Holds initial a (zeroWord.take 24))
    (left0 : initial (a-2)=false) (earlier : initial (a-1)=true)
    (absent : initial (a-3)=false)
    (frame : ∀ q, q<a+24 → out q=initial q) :
    silentSegment machine (cfg 83 (a+23) out) (cfg 92 (a-4) out) 27 := by
  have hprefix' : Holds out a (zeroWord.take 24) := by
    apply holds_transport initial out _ _ hpre
    intro q _ hq
    have hlen : (zeroWord.take 24).length=24 := by decide
    rw [hlen] at hq
    symm
    exact frame q (by omega)
  have hleft : Holds out (a-3) [false,false,true] := by
    simp only [Holds]
    refine ⟨?_,?_,?_,trivial⟩
    · rw [frame _ (by omega)]; exact absent
    · rw [show a-3+1=a-2 by omega,frame _ (by omega)]; exact left0
    · rw [show a-3+1+1=a-1 by omega,frame _ (by omega)]; exact earlier
  have hword : Holds out (a-3) scanWord := by
    apply holds_append_intro out (a-3) [false,false,true] (zeroWord.take 24) hleft
    have hp : a-3+(([false,false,true].length : Nat):Int)=a := by norm_num
    rw [hp]
    exact hprefix'
  have hdown := holds_reverse out (a-3) scanWord hword
  rw [scan_word_reverse,scan_word_length] at hdown
  have hp : a-3+((27 : Nat):Int)-1=a+23 := by omega
  rw [hp] at hdown
  have hs := (chain_blocks chain83 scanCounts (a+23) out [] (by decide) (by simpa using hdown)).2
  have hlen : (blocks scanCounts).length=27 := by decide
  rw [hlen] at hs
  have hh : a+23-((27 : Nat):Int)=a-4 := by omega
  simpa only [hh] using hs

/-- Retain the earlier full-window interface. -/
theorem positive_return_to92 (a : Int) (initial out : Int → Bool)
    (window : Holds initial a zeroWord)
    (left0 : initial (a-2)=false) (earlier : initial (a-1)=true)
    (absent : initial (a-3)=false)
    (frame : ∀ q, q<a+24 → out q=initial q) :
    silentSegment machine (cfg 83 (a+23) out) (cfg 92 (a-4) out) 27 := by
  have hpre := holds_prefix_word initial a (zeroWord.take 24) (zeroWord.drop 24) (by
    simpa only [List.take_append_drop] using window)
  exact positive_return_to92_with_prefix a initial out hpre left0 earlier absent frame

/-- The cell before the adjacent zeros selects one of two exact state-93
anchors; both branches preserve the tape and emit no event. -/
theorem positive_return_dispatch_with_prefix (a : Int) (initial out : Int → Bool)
    (hpre : Holds initial a (zeroWord.take 24))
    (left0 : initial (a-2)=false) (earlier : initial (a-1)=true)
    (absent : initial (a-3)=false)
    (frame : ∀ q, q<a+24 → out q=initial q) :
    (initial (a-4)=true → silentSegment machine (cfg 83 (a+23) out) (cfg 93 (a-3) out) 28) ∧
    (initial (a-4)=false → silentSegment machine (cfg 83 (a+23) out) (cfg 93 a out) 31) := by
  have hs := positive_return_to92_with_prefix a initial out hpre left0 earlier absent frame
  have hz3 : out (a-3)=false := (frame _ (by omega)).trans absent
  have hz2 : out (a-2)=false := (frame _ (by omega)).trans left0
  have ho1 : out (a-1)=true := (frame _ (by omega)).trans earlier
  constructor
  · intro before
    have hb : out (a-4)=true := (frame _ (by omega)).trans before
    have hstep : silentSegment machine (cfg 92 (a-4) out) (cfg 93 (a-3) out) 1 := by
      simpa only [show a-4+1=a-3 by omega] using oneSeg machine _ _ (step92_one (a-4) out hb)
    simpa using segAdd machine _ _ _ 27 1 hs hstep
  · intro before
    have hb : out (a-4)=false := (frame _ (by omega)).trans before
    have hfirst : silentSegment machine (cfg 92 (a-4) out) (cfg 92 (a-3) out) 1 := by
      simpa only [show a-4+1=a-3 by omega] using oneSeg machine _ _ (step92_zero (a-4) out hb)
    have hsecond : silentSegment machine (cfg 92 (a-3) out) (cfg 92 (a-2) out) 1 := by
      simpa only [show a-3+1=a-2 by omega] using oneSeg machine _ _ (step92_zero (a-3) out hz3)
    have hthird : silentSegment machine (cfg 92 (a-2) out) (cfg 92 (a-1) out) 1 := by
      simpa only [show a-2+1=a-1 by omega] using oneSeg machine _ _ (step92_zero (a-2) out hz2)
    have hfourth : silentSegment machine (cfg 92 (a-1) out) (cfg 93 a out) 1 := by
      simpa only [show a-1+1=a by omega] using oneSeg machine _ _ (step92_one (a-1) out ho1)
    have h12 := segAdd machine _ _ _ 1 1 hfirst hsecond
    have h123 := segAdd machine _ _ _ 2 1 h12 hthird
    have h1234 := segAdd machine _ _ _ 3 1 h123 hfourth
    simpa using segAdd machine _ _ _ 27 4 hs h1234

/-- Retain the earlier full-window dispatch interface. -/
theorem positive_return_dispatch (a : Int) (initial out : Int → Bool)
    (window : Holds initial a zeroWord)
    (left0 : initial (a-2)=false) (earlier : initial (a-1)=true)
    (absent : initial (a-3)=false)
    (frame : ∀ q, q<a+24 → out q=initial q) :
    (initial (a-4)=true → silentSegment machine (cfg 83 (a+23) out) (cfg 93 (a-3) out) 28) ∧
    (initial (a-4)=false → silentSegment machine (cfg 83 (a+23) out) (cfg 93 a out) 31) := by
  have hpre := holds_prefix_word initial a (zeroWord.take 24) (zeroWord.drop 24) (by
    simpa only [List.take_append_drop] using window)
  exact positive_return_dispatch_with_prefix a initial out hpre left0 earlier absent frame

/-- Compose the supplied padded cycle, positive selector, and the two
possible physical dispatches. The finite suffix remains available. -/
theorem padded_absent_positive_dispatch_with_control (a : Int) (r v : Nat) (rest : List Nat)
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
      (t (a-4)=true → silentSegment machine (cfg 93 a t) (cfg 93 (a-3) out) (n+28)) ∧
      (t (a-4)=false → silentSegment machine (cfg 93 a t) (cfg 93 a out) (n+31)) := by
  obtain ⟨n,out,hn,hseg,hmark,hblank,hcorr,hstop,hbank,hframe⟩ :=
    padded_absent_next_positive_with_control a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  have hbank' := positive_bank_extended_with_suffix (a+36+(r : Int)) v rest suffix out hbank
  obtain ⟨hleft,hright⟩ := positive_return_dispatch a t out window left0 earlier absent hframe
  refine ⟨n,out,hn,hbank',hmark,hblank,hcorr,hstop,hframe,?_,?_⟩
  · intro h
    exact segAdd machine _ _ _ n 28 hseg (hleft h)
  · intro h
    exact segAdd machine _ _ _ n 31 hseg (hright h)

/-- Retain the earlier suffix-preserving dispatch interface. -/
theorem padded_absent_positive_dispatch (a : Int) (r v : Nat) (rest : List Nat)
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
      (∀ q, q<a+24 → out q=t q) ∧
      (t (a-4)=true → silentSegment machine (cfg 93 a t) (cfg 93 (a-3) out) (n+28)) ∧
      (t (a-4)=false → silentSegment machine (cfg 93 a t) (cfg 93 a out) (n+31)) := by
  obtain ⟨n,out,hn,hbank,_hmark,_hblank,_hcorr,_hstop,hframe,hleft,hright⟩ :=
    padded_absent_positive_dispatch_with_control a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨n,out,hn,hbank,hframe,hleft,hright⟩

#print axioms scan_word_reverse
#print axioms positive_return_to92
#print axioms positive_return_to92_with_prefix
#print axioms positive_return_dispatch
#print axioms positive_return_dispatch_with_prefix
#print axioms padded_absent_positive_dispatch
#print axioms padded_absent_positive_dispatch_with_control
end Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
