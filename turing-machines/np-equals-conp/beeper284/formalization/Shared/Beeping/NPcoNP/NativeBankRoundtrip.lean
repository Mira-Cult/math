import Shared.Beeping.NPcoNP.NativeZeroRestore
import Shared.Beeping.NPcoNP.Native54Prepare

/-! Common reverse-and-forward control scan, independent of the cell
following the touched bank marker. -/
namespace Shared.Beeping.NPcoNP.NativeBankRoundtrip
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeZeroRestore
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- The round trip reaches state 17 just after the touched target; the next
cell is deliberately unconstrained. -/
theorem roundtrip (t : Int → Bool) (mark pos : Int) (xs ys : List Bool)
    (hx : Prefix xs) (hy : Prefix ys) (hlen : xs.length=ys.length)
    (hpos : pos=mark+(xs.length : Int)+4)
    (left : downHolds t (pos-2) (xs ++ [false,false]))
    (hmark : t mark=true) (hz1 : t (mark+1)=false) (hz2 : t (mark+2)=false)
    (right : Holds t (mark+3) (ys ++ [false,false])) :
    let u := setAt (mark+2) (clearAt mark t)
    silentSegment machine (cfg 262 (pos-2) t) (cfg 17 (pos+1) u) (2*xs.length+7) := by
  dsimp only
  let u0 := clearAt mark t
  let u := setAt (mark+2) u0
  have hleft := scan262 xs hx (pos-2) t left
  have hleft' : silentSegment machine (cfg 262 (pos-2) t) (cfg 264 mark t) (xs.length+2) := by
    have he : pos-2-(xs.length : Int)-2=mark := by omega
    simpa only [he] using hleft
  have hu1 : u0 (mark+1)=false := by
    simp [u0,clearAt,show mark+1≠mark by omega,hz1]
  have hu2 : u0 (mark+2)=false := by
    simp [u0,clearAt,show mark+2≠mark by omega,hz2]
  have a := oneSeg machine _ _ (step264_one mark t hmark)
  have b := oneSeg machine _ _ (step49_zero (mark+1) u0 hu1)
  have c := oneSeg machine _ _ (step267_zero (mark+2) u0 hu2)
  have ab := segAdd machine _ _ _ 1 1 a b
  have ab' : silentSegment machine (cfg 264 mark t) (cfg 267 (mark+2) u0) 2 := by
    have he : mark+1+1=mark+2 := by omega
    simpa [u0,he] using ab
  have abc := segAdd machine _ _ _ 2 1 ab' c
  have abc' : silentSegment machine (cfg 264 mark t) (cfg 268 (mark+3) u) 3 := by
    have he : mark+2+1=mark+3 := by omega
    simpa [u,he] using abc
  have huword : Holds u (mark+3) (ys ++ [false,false]) := by
    apply holds_transport t u (mark+3) _ right
    intro q hq _
    simp [u,u0,setAt,clearAt,show q≠mark by omega,show q≠mark+2 by omega]
  have hforward := scan268 ys hy (mark+3) u huword
  have hforward' : silentSegment machine (cfg 268 (mark+3) u) (cfg 17 (pos+1) u)
      (ys.length+2) := by
    have he : mark+3+(ys.length : Int)+2=pos+1 := by omega
    simpa only [he] using hforward
  have hfirst := segAdd machine _ _ _ (xs.length+2) 3 hleft' abc'
  have all := segAdd machine _ _ _ (xs.length+2+3) (ys.length+2) hfirst hforward'
  have htime : xs.length+2+3+(ys.length+2)=2*xs.length+7 := by omega
  simpa only [htime,u,u0] using all

/-- Drop a known silent first transition from a silent finite segment. -/
theorem silent_tail {n : Nat} (M : Machine n) (c d e : Config n) (k : Nat)
    (step : M.step c=(d,false)) (seg : silentSegment M c e (k+1)) :
    silentSegment M d e k := by
  have first := oneSeg M c d step
  rcases first with ⟨hadvance,hword⟩
  rcases seg with ⟨hseg,hsegword⟩
  have hk : k+1=1+k := by omega
  rw [hk,WordEventSystem.advance_add,hadvance] at hseg
  rw [hk,WordEventSystem.wordFrom_add,hadvance,hword,List.nil_append] at hsegword
  exact ⟨hseg,hsegword⟩

#print axioms roundtrip
#print axioms silent_tail
end Shared.Beeping.NPcoNP.NativeBankRoundtrip
