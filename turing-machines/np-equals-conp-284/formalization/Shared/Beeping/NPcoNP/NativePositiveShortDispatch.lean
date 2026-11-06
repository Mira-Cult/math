import Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch

/-! A short physical delimiter scan with three supplied earlier blanks. -/
namespace Shared.Beeping.NPcoNP.NativePositiveShortDispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

def shortWord : List Bool := [false,false] ++ zeroWord.take 24
def shortCounts : List Nat := List.replicate 12 1 ++ [0,0]
theorem short_word_reverse : shortWord.reverse=blocks shortCounts := by decide
theorem short_word_length : shortWord.length=26 := by decide

/-- The fourteen physical delimiters consist of twelve zero-value blocks and
 two adjacent blanks. An additional preceding blank selects the return anchor. -/
theorem positive_short_dispatch (a : Int) (initial out : Int → Bool)
    (hpre : Holds initial a (zeroWord.take 24))
    (h1 : initial (a-1)=false) (h2 : initial (a-2)=false) (h3 : initial (a-3)=false)
    (frame : ∀ q, q<a+24 → out q=initial q) :
    silentSegment machine (cfg 83 (a+23) out) (cfg 93 (a+2) out) 31 := by
  have hp : Holds out a (zeroWord.take 24) := by
    apply holds_transport initial out _ _ hpre
    intro q _ hq
    have hl : (zeroWord.take 24).length=24 := by decide
    rw [hl] at hq
    exact (frame q (by omega)).symm
  have hleft : Holds out (a-2) [false,false] := by
    simp only [Holds]
    exact ⟨(frame _ (by omega)).trans h2,
      by simpa only [show a-2+1=a-1 by omega] using (frame _ (by omega)).trans h1,trivial⟩
  have hword : Holds out (a-2) shortWord := by
    apply holds_append_intro out (a-2) [false,false] (zeroWord.take 24) hleft
    have he : a-2+(([false,false].length : Nat):Int)=a := by norm_num
    rw [he]
    exact hp
  have hdown := holds_reverse out (a-2) shortWord hword
  rw [short_word_reverse,short_word_length] at hdown
  have hh : a-2+((26 : Nat):Int)-1=a+23 := by omega
  rw [hh] at hdown
  have hs := (chain_blocks chain83 shortCounts (a+23) out [] (by decide) (by simpa using hdown)).2
  have hl : (blocks shortCounts).length=26 := by decide
  rw [hl] at hs
  have hs' : silentSegment machine (cfg 83 (a+23) out) (cfg 92 (a-3) out) 26 := by
    have hh' : a+23-((26 : Nat):Int)=a-3 := by omega
    simpa only [hh'] using hs
  have hz3 : out (a-3)=false := (frame _ (by omega)).trans h3
  have hz2 : out (a-2)=false := (frame _ (by omega)).trans h2
  have hz1 : out (a-1)=false := (frame _ (by omega)).trans h1
  have hz0 : out a=false := by
    have h := holds_get out a (zeroWord.take 24) hp 0 (by decide)
    have hv : (zeroWord.take 24)[0]=false := by decide
    rw [hv] at h
    simpa using h
  have ho1 : out (a+1)=true := by
    have h := holds_get out a (zeroWord.take 24) hp 1 (by decide)
    have hv : (zeroWord.take 24)[1]=true := by decide
    rw [hv] at h
    simpa using h
  have s1 : silentSegment machine (cfg 92 (a-3) out) (cfg 92 (a-2) out) 1 := by
    simpa only [show a-3+1=a-2 by omega] using oneSeg machine _ _ (step92_zero (a-3) out hz3)
  have s2 : silentSegment machine (cfg 92 (a-2) out) (cfg 92 (a-1) out) 1 := by
    simpa only [show a-2+1=a-1 by omega] using oneSeg machine _ _ (step92_zero (a-2) out hz2)
  have s3 : silentSegment machine (cfg 92 (a-1) out) (cfg 92 a out) 1 := by
    simpa only [show a-1+1=a by omega] using oneSeg machine _ _ (step92_zero (a-1) out hz1)
  have s4 : silentSegment machine (cfg 92 a out) (cfg 92 (a+1) out) 1 :=
    oneSeg machine _ _ (step92_zero a out hz0)
  have s5 : silentSegment machine (cfg 92 (a+1) out) (cfg 93 (a+2) out) 1 := by
    simpa only [show a+1+1=a+2 by omega] using oneSeg machine _ _ (step92_one (a+1) out ho1)
  have s12 := segAdd machine _ _ _ 1 1 s1 s2
  have s123 := segAdd machine _ _ _ 2 1 s12 s3
  have s1234 := segAdd machine _ _ _ 3 1 s123 s4
  have s12345 := segAdd machine _ _ _ 4 1 s1234 s5
  simpa using segAdd machine _ _ _ 26 5 hs' s12345

#print axioms positive_short_dispatch
end Shared.Beeping.NPcoNP.NativePositiveShortDispatch
