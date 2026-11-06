import Shared.Beeping.NPcoNP.NativeRow9Window
import Shared.Beeping.NPcoNP.NativeRow9ControlScan

/-! Restore the second bank block's first bit and reach the paid increment
entry. This theorem uses supplied finite words and does not assert reachability. -/
namespace Shared.Beeping.NPcoNP.NativeRow9Restore
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeZeroRestore
open Shared.Beeping.NPcoNP.NativeRow9ControlScan
open Shared.Beeping.NPcoNP.NativeRow9Window
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The return scan reaches the control zeros, writes a return marker,
replays the word and restores the temporarily cleared bank bit. -/
theorem restore_to14 (h separator : Int) (t : Int → Bool) (a b : Nat) (tail : List Bool)
    (hlong : h+12≤separator) (h8 : t (h+8)=false)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (control : ∀ q, h+11≤q → q<separator → t q=true) (hsep : t separator=false)
    (bank : Holds t (separator+1) (block a ++ (block b ++ tail))) :
    let r := (separator-(h+12)).toNat
    let ys := unaryBankPrefix r [a]
    let pos := separator+1+((a+2 : Nat):Int)
    silentSegment machine (cfg 262 (pos-2) (clearAt pos t))
      (cfg 14 (pos+1) (setAt (h+10) t)) (2*ys.length+7) := by
  dsimp only
  let r := (separator-(h+12)).toNat
  let ys := unaryBankPrefix r [a]
  let pos := separator+1+((a+2 : Nat):Int)
  let u := clearAt pos t
  obtain ⟨hyp,hyrev,hback,hforward,hpos⟩ := windows h separator t a b tail hlong h9 h10 control hsep bank
  have hpos' : pos=(h+8)+(ys.length : Int)+4 := hpos
  have hscan := scan262 ys.reverse hyrev (pos-2) u hback
  have hback' : silentSegment machine (cfg 262 (pos-2) u) (cfg 264 (h+8) u) (ys.length+2) := by
    have he : pos-2-((ys.length : Nat):Int)-2=h+8 := by omega
    simpa only [List.length_reverse,he] using hscan
  have hu8 : u (h+8)=false := by simp [u,clearAt,show h+8≠pos by dsimp [pos]; omega,h8]
  have hu9 : u (h+9)=false := by simp [u,clearAt,show h+9≠pos by dsimp [pos]; omega,h9]
  have hu10 : u (h+10)=false := by simp [u,clearAt,show h+10≠pos by dsimp [pos]; omega,h10]
  have a1 := oneSeg machine _ _ (step264_zero (h+8) u hu8)
  have a2 := oneSeg machine _ _ (step44_zero (h+9) u hu9)
  have a3 := oneSeg machine _ _ (step29_zero (h+10) u hu10)
  have aa : silentSegment machine (cfg 264 (h+8) u) (cfg 265 (h+11) (setAt (h+10) u)) 3 := by
    have a1' : silentSegment machine (cfg 264 (h+8) u) (cfg 44 (h+9) u) 1 := by
      simpa only [show h+8+1=h+9 by omega] using a1
    have a2' : silentSegment machine (cfg 44 (h+9) u) (cfg 29 (h+10) u) 1 := by
      simpa only [show h+9+1=h+10 by omega] using a2
    have ab := segAdd machine _ _ _ 1 1 a1' a2'
    have all := segAdd machine _ _ _ 2 1 ab a3
    simpa only [show h+10+1=h+11 by omega] using all
  let u' := setAt (h+10) u
  have hforward' : Holds u' (h+11) (ys ++ [false,false]) := by
    apply holds_transport u u' _ _ hforward
    intro q hq _
    simp [u',setAt,show q≠h+10 by omega]
  have hfor := scan265 ys hyp (h+11) u' hforward'
  have hfor' : silentSegment machine (cfg 265 (h+11) u')
      (cfg 14 (pos+1) (setAt pos u')) (ys.length+2) := by
    have he : h+11+(ys.length : Int)+1=pos := by omega
    have he' : h+11+(ys.length : Int)+2=pos+1 := by omega
    simpa only [he,he'] using hfor
  have htarget : t pos=true := by
    have htail := holds_append_tail t (separator+1) (block a) (block b ++ tail) bank
    have he : separator+1+((block a).length : Int)=pos := by simp [block_length,pos]
    rw [he] at htail
    simp only [block,List.replicate_succ,List.cons_append,Holds] at htail
    exact htail.1
  have htape : setAt pos u'=setAt (h+10) t := by
    funext q
    by_cases hq : q=pos
    · subst q
      simp [u',u,setAt,clearAt,show pos≠h+10 by dsimp [pos]; omega,htarget]
    · by_cases hm : q=h+10
      · subst q
        simp [u',u,setAt,clearAt,hq]
      · simp [u',u,setAt,clearAt,hq,hm]
  rw [htape] at hfor'
  have pre := segAdd machine _ _ _ (ys.length+2) 3 hback' aa
  have all := segAdd machine _ _ _ (ys.length+2+3) (ys.length+2) pre hfor'
  have hn : ys.length+2+3+(ys.length+2)=2*ys.length+7 := by omega
  simpa only [hn,r,ys,pos,u,u'] using all

#print axioms restore_to14
end Shared.Beeping.NPcoNP.NativeRow9Restore
