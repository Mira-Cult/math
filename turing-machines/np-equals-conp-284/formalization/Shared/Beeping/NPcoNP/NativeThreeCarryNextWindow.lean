import Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
import Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
import Shared.Beeping.NPcoNP.NativeHalfBankFirst
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Recover the next all-zero selector to the left of the three-one
return. The preceding marker is retained as an explicit input cell. -/
namespace Shared.Beeping.NPcoNP.NativeThreeCarryNextWindow
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The return's tape update leaves the entire ray left of its new marker
unchanged, independently of any execution or layout hypothesis. -/
theorem output_left (d : Int) (r : Nat) (t : Int → Bool) (q : Int)
    (hq : q<d-4) : outTape d r t q=t q := by
  change put (clearRange (scanTape d t) (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true q=t q
  rw [put_other _ _ _ _ (by omega)]
  change (if d+3≤q ∧ q<d+2+(r : Int) then false else scanTape d t q)=t q
  rw [if_neg (by omega)]
  change put (carryTape d t) (d+2) false q=t q
  rw [put_other _ _ _ _ (by omega)]
  change put (cleared t (d-1) 3) ((d-1)-((3 : Nat):Int)) true q=t q
  rw [put_other _ _ _ _ (by omega)]
  change (if (d-1)-((3 : Nat):Int)<q ∧ q≤d-1 then false else t q)=t q
  rw [if_neg (by omega)]

/-- The next fourteen-block all-zero window is two cells left of the old
one, provided the two additional cells are supplied. Its earlier marker is
preserved, not manufactured by the return. -/
theorem next_window (a : Int) (r : Nat) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (left1 : t (a-1)=true) :
    Holds (outTape (a+30) r t) (a-2)
      (markerWindow (List.replicate 13 0 ++ [0])) ∧
    outTape (a+30) r t (a-3)=t (a-3) := by
  let short := markerWindow (List.replicate 13 0)
  have oldWord : markerWindow (List.replicate 13 0 ++ [0]) = short ++ [false,true] := by
    dsimp [short]
    decide
  have newWord : markerWindow (List.replicate 13 0 ++ [0]) = [false,true] ++ short := by
    dsimp [short]
    decide
  have hs : Holds t a short := by
    apply holds_prefix_word t a short [false,true]
    rw [← oldWord]
    exact window
  have hl : Holds t (a-2) [false,true] := by
    simp only [Holds]
    have hp : a-2+1=a-1 := by omega
    rw [hp]
    exact ⟨left0,left1,trivial⟩
  have hpos : a-2+(([false,true].length : Nat):Int)=a := by simp
  have hw := holds_append_intro t (a-2) [false,true] short hl (by rw [hpos]; exact hs)
  have hw' : Holds (outTape (a+30) r t) (a-2) ([false,true]++short) := by
    apply holds_transport t _ _ _ hw
    intro q _ hq
    have hlen : ([false,true]++short).length=28 := by
      dsimp [short]
      decide
    rw [hlen] at hq
    exact (output_left (a+30) r t q (by omega)).symm
  constructor
  · rw [newWord]
    exact hw'
  · exact output_left (a+30) r t (a-3) (by omega)

/-- Under the local carry pattern, the table reaches the next all-zero
window at its exact head position. The prior marker's value is preserved,
so both its present and absent cases remain visible. -/
theorem return_next_window (a : Int) (r : Nat) (t : Int → Bool)
    (hr : 0<r)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (left1 : t (a-1)=true)
    (c2 : t (a+28)=true) (c3 : t (a+29)=true)
    (z0 : t (a+30)=false) (z1 : t (a+31)=false)
    (ones : ∀ i : Nat, i<r → t (a+32+(i : Int))=true)
    (stop : t (a+32+(r : Int))=false) :
    silentSegment machine (cfg 23 (a+31+(r : Int)) t)
      (cfg 83 (a+25) (outTape (a+30) r t)) (3*r+18) ∧
    Holds (outTape (a+30) r t) (a-2)
      (markerWindow (List.replicate 13 0 ++ [0])) ∧
    outTape (a+30) r t (a-3)=t (a-3) ∧
    outTape (a+30) r t (a+26)=true := by
  have h0 := holds_get t a (markerWindow (List.replicate 13 0 ++ [0])) window 26 (by decide)
  have h1 := holds_get t a (markerWindow (List.replicate 13 0 ++ [0])) window 27 (by decide)
  have b0 : (markerWindow (List.replicate 13 0 ++ [0]))[26]=false := by decide
  have b1 : (markerWindow (List.replicate 13 0 ++ [0]))[27]=true := by decide
  rw [b0] at h0
  rw [b1] at h1
  have c0 : t (a+26)=false := by simpa using h0
  have c1 : t (a+27)=true := by simpa using h1
  obtain ⟨hseg,hmark,_hframe⟩ := return_exact (a+30) r t hr
    (by
      have hp : a+30-4=a+26 := by omega
      rw [hp]; exact c0)
    (by
      have hp : a+30-3=a+27 := by omega
      rw [hp]; exact c1)
    (by
      have hp : a+30-2=a+28 := by omega
      rw [hp]; exact c2)
    (by
      have hp : a+30-1=a+29 := by omega
      rw [hp]; exact c3)
    z0
    (by
      have hp : a+30+1=a+31 := by omega
      rw [hp]; exact z1)
    (by
      intro i hi
      have hp : a+30+2+(i : Int)=a+32+(i : Int) := by omega
      rw [hp]; exact ones i hi)
    (by
      have hp : a+30+2+(r : Int)=a+32+(r : Int) := by omega
      rw [hp]; exact stop)
  have hp : a+30+1+(r : Int)=a+31+(r : Int) := by omega
  have hh : a+30-5=a+25 := by omega
  have hm : a+30-4=a+26 := by omega
  rw [hp,hh] at hseg
  rw [hm] at hmark
  exact ⟨hseg,(next_window a r t window left0 left1).1,
    (next_window a r t window left0 left1).2,hmark⟩

#print axioms output_left
#print axioms next_window
#print axioms return_next_window
end Shared.Beeping.NPcoNP.NativeThreeCarryNextWindow
