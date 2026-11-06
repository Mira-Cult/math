import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! Cancel the temporary clearing and filling in a terminal selector return. -/
namespace Shared.Beeping.NPcoNP.NativeTerminalControlAlgebra
open Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- Once the supplied one-run is restored by state 10, the compound tape
update equals setting exactly the two adjacent control-marker cells. -/
theorem restore_control (r : Nat) (h : Int) (t : Int → Bool)
    (hr : 0<r) (run : Holds t (h+2) (List.replicate r true ++ [false])) :
    let u := put (put t (h-1) true) (h+2) false
    let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
    fillRange (setAt h out) (h+2) (h+1+(r : Int)) = setAt (h-1) (setAt h t) := by
  dsimp only
  funext p
  have hon : ∀ q, h+2≤q → q≤h+1+(r : Int) → t q=true := by
    intro q hq hq'
    let i := (q-(h+2)).toNat
    have hi : (i : Int)=q-(h+2) := Int.toNat_of_nonneg (by omega)
    have hir : i<r := by omega
    have hb := holds_get t (h+2) (List.replicate r true ++ [false]) run i (by simp; omega)
    have he : h+2+(i : Int)=q := by omega
    rw [he] at hb
    simpa [hir] using hb
  by_cases hp : p=h-1
  · subst p
    simp only [fillRange,setAt,put,clearRange]
    split_ifs <;> simp_all <;> omega
  · by_cases hh : p=h
    · subst p
      simp only [fillRange,setAt,put,clearRange]
      split_ifs <;> simp_all
    · by_cases hrun : h+2≤p ∧ p≤h+1+(r : Int)
      · have htrue : t p=true := hon p hrun.1 hrun.2
        by_cases hend : p=h+1+(r : Int)
        · rw [hend] at htrue
          simp [fillRange,setAt,put,hend,htrue]
        · have hf : h+2≤p ∧ p<h+1+(r : Int) := by omega
          simp [fillRange,hf,setAt,hp,hh,htrue]
      · have hf : ¬(h+2≤p ∧ p<h+1+(r : Int)) := by omega
        have hc : ¬(h+3≤p ∧ p<h+2+(r : Int)) := by omega
        have hend : p≠h+1+(r : Int) := by omega
        have hfirst : p≠h+2 := by omega
        simp [fillRange,hf,setAt,put,clearRange,hc,hend,hfirst,hp,hh]

#print axioms restore_control
end Shared.Beeping.NPcoNP.NativeTerminalControlAlgebra
