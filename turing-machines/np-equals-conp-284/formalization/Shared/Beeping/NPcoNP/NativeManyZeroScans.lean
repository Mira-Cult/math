import Shared.Beeping.NPcoNP.NativeManyZeroEntry
import Shared.Beeping.NPcoNP.NativeManySelectorReturn
import Shared.Beeping.NPcoNP.NativeHalfScannerFrames
import Shared.Beeping.NPcoNP.UnaryBank

/-! Zero-valued bank after the two paid state-15/11 scans. Finite left
return delimiters are explicit; no recurring layout is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeManyZeroScans
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeManySelectorReturn
open Shared.Beeping.NPcoNP.NativeManyZeroEntry
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

/-- Both scans followed by the zero-bank failure return have a finite
silent execution. The whole encoded bank and its trailing blanks survive. -/
theorem scans_zero_to1 (p n k : Nat) (vs : List Nat) (h : Int) (t : Int → Bool) (s : Shape)
    (first : Holds t h (List.replicate p true ++ [false]))
    (second : Holds t (h+(p : Int)+1) (List.replicate n true ++ [false]))
    (bank : Holds t (h+(p : Int)+(n : Int)+2) (encode (0::vs) ++ [false,false]))
    (hprefix : downHolds t (h+(p : Int)+(n : Int)+1) (bits s ++ [false,false]))
    (stop : t (h+(p : Int)+(n : Int)+1-(bits s).length-2-(k : Int))=false) :
    let x := h+(p : Int)+(n : Int)+2
    let pos := x-1-(bits s).length-2
    ∃ m : Nat, 0<m ∧ m≤k+1 ∧
      let out := clearRange t (pos-(m : Int)+2) (pos+1)
      Holds out x (encode (0::vs) ++ [false,false]) ∧
      (∀ z, x-1≤z → out z=t z) ∧
      silentSegment machine (cfg 15 h t) (cfg 1 (pos-(m : Int)) out)
        (p+n+(bits s).length+m+7) := by
  dsimp only
  let x := h+(p : Int)+(n : Int)+2
  let pos := x-1-(bits s).length-2
  have bank' : Holds t x (block 0 ++ (encode vs ++ [false,false])) := by
    simpa [x,encode,List.append_assoc] using bank
  simp only [block_zero,List.cons_append,Holds] at bank'
  have h0 : t x=true := bank'.1
  have h1 : t (x+1)=false := bank'.2.1
  have hprefix' : downHolds t (x-1) (bits s ++ [false,false]) := by
    have he : h+(p : Int)+(n : Int)+1=x-1 := by dsimp [x]; omega
    rw [he] at hprefix
    exact hprefix
  have hstop' : t (x-1-(bits s).length-2-(k : Int))=false := by
    have he : x-1=h+(p : Int)+(n : Int)+1 := by dsimp [x]; omega
    rw [he]
    exact stop
  obtain ⟨m,hm,hbound,hframe,hzero⟩ := zero_to1 x t s k h0 h1 hprefix' hstop'
  let out := clearRange t (pos-(m : Int)+2) (pos+1)
  have hframe' : ∀ z, x-1≤z → out z=t z := by
    intro z hz
    apply hframe
    omega
  have hbank : Holds out x (encode (0::vs) ++ [false,false]) := by
    apply holds_transport t out x _ bank
    intro z hz _
    symm
    exact hframe' z (by omega)
  have hs1 := scan15 p h t first
  have hs2 := scan11 n (h+(p : Int)+1) t second
  have h12 := segAdd machine _ _ _ (p+1) (n+1) hs1 hs2
  have h12' : silentSegment machine (cfg 15 h t) (cfg 13 x t) (p+1+(n+1)) := by
    have he : h+(p : Int)+1+(n : Int)+1=x := by dsimp [x]; omega
    simpa only [he] using h12
  have hall := segAdd machine _ _ _ (p+1+(n+1)) (3+((bits s).length+2)+m) h12' hzero
  have hc : p+1+(n+1)+(3+((bits s).length+2)+m)=p+n+(bits s).length+m+7 := by omega
  rw [hc] at hall
  exact ⟨m,hm,hbound,hbank,hframe',hall⟩

#print axioms scans_zero_to1
end Shared.Beeping.NPcoNP.NativeManyZeroScans
