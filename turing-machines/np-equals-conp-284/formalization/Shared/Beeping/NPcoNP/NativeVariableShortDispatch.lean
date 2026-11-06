import Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
import Shared.Beeping.NPcoNP.NativeMarkerExtraZeroReturn
import Shared.Beeping.NPcoNP.NativeFirstDispatch

/-! A 14-delimiter return scan with a variable number of short zero blocks. -/
namespace Shared.Beeping.NPcoNP.NativeVariableShortDispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeMarkerExtraZeroReturn
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeIncBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

/-- The complete finite family of physical delimiter words, for the 14-row
selector, agrees with the corresponding backwards scan counts. -/
theorem variable_scan_words : ∀ m : Fin 15,
    (List.replicate (14-m.val) false ++ zeroPairs m.val).reverse =
      blocks (List.replicate m.val 1 ++ List.replicate (14-m.val) 0) := by decide

/-- Any positive number of alternating blocks up to 14, preceded by a blank
ray, returns the literal 14-delimiter selector to the same state-93 anchor
in exactly 31 silent steps. -/
theorem variable_short_dispatch (t : Int → Bool) (a : Int) (m : Nat)
    (hm : 0<m) (hm14 : m≤14) (hprefix : Holds t a (zeroPairs m))
    (blank : ∀ q, q<a → t q=false) :
    silentSegment machine (cfg 83 (a+((2*m : Nat):Int)-1) t) (cfg 93 (a+2) t) 31 := by
  let z := 14-m
  let word := List.replicate z false ++ zeroPairs m
  let counts := List.replicate m 1 ++ List.replicate z 0
  have hmz : m+z=14 := by dsimp [z]; omega
  have hzeros : Holds t (a-(z : Int)) (List.replicate z false) := by
    apply holds_of_get
    intro i hi
    have hi' : i<z := by simpa using hi
    simp only [List.getElem_replicate]
    apply blank
    omega
  have hword : Holds t (a-(z : Int)) word := by
    apply holds_append_intro t (a-(z : Int)) (List.replicate z false) (zeroPairs m) hzeros
    have hp : a-(z : Int)+((List.replicate z false).length : Int)=a := by simp
    rw [hp]
    exact hprefix
  have hlen : word.length=z+2*m := by simp [word,zeroPairs_length]
  have hreverse : word.reverse=blocks counts := by
    have hh := variable_scan_words ⟨m,by omega⟩
    simpa only [word,counts,z] using hh
  have hd := holds_reverse t (a-(z : Int)) word hword
  rw [hreverse,hlen] at hd
  have hp : a-(z : Int)+((z+2*m : Nat):Int)-1=a+((2*m : Nat):Int)-1 := by push_cast; omega
  rw [hp] at hd
  have hcount : counts.length=14 := by simp [counts,hmz]
  have hscan := (chain_blocks chain83 counts _ t [] hcount (by simpa using hd)).2
  have hblocks : (blocks counts).length=z+2*m := by
    have hh := congrArg List.length hreverse
    simpa only [List.length_reverse,hlen] using hh.symm
  rw [hblocks] at hscan
  have hscan' : silentSegment machine (cfg 83 (a+((2*m : Nat):Int)-1) t)
      (cfg 92 (a-(z : Int)-1) t) (z+2*m) := by
    push_cast at hscan ⊢
    have hp' : a+2*(m : Int)-1-((z : Int)+2*(m : Int))=a-(z : Int)-1 := by omega
    simpa only [hp'] using hscan
  have hzero0 : t a=false := by
    cases m with
    | zero => omega
    | succ m =>
      simp only [zeroPairs,List.cons_append,Holds] at hprefix
      exact hprefix.1
  have hone1 : t (a+1)=true := by
    cases m with
    | zero => omega
    | succ m =>
      simp only [zeroPairs,List.cons_append,Holds] at hprefix
      exact hprefix.2.1
  have h92 := scan92_exact (z+2) (a-(z : Int)-1) t (by
    intro i hi
    have hi' : i≤z+1 := by omega
    by_cases hi0 : i=z+1
    · have hp' : a-(z : Int)-1+(i : Int)=a := by omega
      rw [hp']; exact hzero0
    · apply blank
      omega) (by
      have hp' : a-(z : Int)-1+((z+2 : Nat):Int)=a+1 := by push_cast; omega
      simpa only [hp'] using hone1)
  have h92' : silentSegment machine (cfg 92 (a-(z : Int)-1) t) (cfg 93 (a+2) t) (z+3) := by
    have hp' : a-(z : Int)-1+((z+2 : Nat):Int)+1=a+2 := by push_cast; omega
    have hc : z+2+1=z+3 := by omega
    simpa only [hp',hc] using h92
  have hall := segAdd machine _ _ _ (z+2*m) (z+3) hscan' h92'
  have hc : z+2*m+(z+3)=31 := by omega
  simpa only [hc] using hall

#print axioms variable_short_dispatch
end Shared.Beeping.NPcoNP.NativeVariableShortDispatch
