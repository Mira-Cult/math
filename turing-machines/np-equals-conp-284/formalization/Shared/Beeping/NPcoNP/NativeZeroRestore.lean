import Shared.Beeping.NPcoNP.NativeZeroRestoreRows
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue

/-! Exact finite reverse and forward cleanup scans. -/
namespace Shared.Beeping.NPcoNP.NativeZeroRestore
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
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- The reverse scan stops at the supplied first adjacent zeros. -/
theorem scan262 (xs : List Bool) (hx : Prefix xs) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (xs ++ [false,false])) :
    silentSegment machine (cfg 262 h t) (cfg 264 (h-(xs.length : Int)-2) t) (xs.length+2) := by
  induction hx generalizing h with
  | nil =>
    simp only [List.nil_append,downHolds] at hm
    have ha := oneSeg machine _ _ (step262_zero h t hm.1)
    have hb := oneSeg machine _ _ (step263_zero (h-1) t hm.2.1)
    have hs := segAdd machine _ _ _ 1 1 ha hb
    have he : h-1-1=h-2 := by omega
    simpa [he] using hs
  | @one xs hx ih =>
    simp only [List.cons_append,downHolds] at hm
    have ha := oneSeg machine _ _ (step262_one h t hm.1)
    have hb := ih (h-1) hm.2
    have hs := segAdd machine _ _ _ 1 (xs.length+2) ha hb
    simpa [Int.sub_sub,Int.add_assoc,Int.add_comm,Int.add_left_comm,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs
  | @zeroOne xs hx ih =>
    simp only [List.cons_append,downHolds] at hm
    have ha := oneSeg machine _ _ (step262_zero h t hm.1)
    have hb := oneSeg machine _ _ (step263_one (h-1) t hm.2.1)
    have hc := ih (h-1-1) hm.2.2
    have hab := segAdd machine _ _ _ 1 1 ha hb
    have hs := segAdd machine _ _ _ 2 (xs.length+2) hab hc
    have he : h-(((false::true::xs).length : Nat) : Int)-2 = h-1-1-(xs.length : Int)-2 := by simp; omega
    have hn : (false::true::xs).length+2=2+(xs.length+2) := by simp; omega
    rw [he,hn]
    exact hs

/-- The forward scan stops just after the supplied adjacent zeros. -/
theorem scan268 (xs : List Bool) (hx : Prefix xs) (h : Int) (t : Int → Bool)
    (hm : Holds t h (xs ++ [false,false])) :
    silentSegment machine (cfg 268 h t) (cfg 17 (h+(xs.length : Int)+2) t) (xs.length+2) := by
  induction hx generalizing h with
  | nil =>
    simp only [List.nil_append,Holds] at hm
    have ha := oneSeg machine _ _ (step268_zero h t hm.1)
    have hb := oneSeg machine _ _ (step269_zero (h+1) t hm.2.1)
    have hs := segAdd machine _ _ _ 1 1 ha hb
    have he : h+1+1=h+2 := by omega
    simpa [he] using hs
  | @one xs hx ih =>
    simp only [List.cons_append,Holds] at hm
    have ha := oneSeg machine _ _ (step268_one h t hm.1)
    have hb := ih (h+1) hm.2
    have hs := segAdd machine _ _ _ 1 (xs.length+2) ha hb
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using hs
  | @zeroOne xs hx ih =>
    simp only [List.cons_append,Holds] at hm
    have ha := oneSeg machine _ _ (step268_zero h t hm.1)
    have hb := oneSeg machine _ _ (step269_one (h+1) t hm.2.1)
    have hc := ih (h+1+1) hm.2.2
    have hab := segAdd machine _ _ _ 1 1 ha hb
    have hs := segAdd machine _ _ _ 2 (xs.length+2) hab hc
    have he : h+(((false::true::xs).length : Nat) : Int)+2 = h+1+1+(xs.length : Int)+2 := by simp; omega
    have hn : (false::true::xs).length+2=2+(xs.length+2) := by simp; omega
    rw [he,hn]
    exact hs

/-- The reverse and forward windows drive the zero-block restoration in
exactly `2*xs.length+9` silent transitions. The three writes are explicit:
clear the control marker, set the nearby return marker, restore the block. -/
theorem restore_zero (t : Int → Bool) (mark pos : Int) (xs ys : List Bool)
    (hx : Prefix xs) (hy : Prefix ys) (hlen : xs.length=ys.length)
    (hpos : pos=mark+(xs.length : Int)+4)
    (left : downHolds t (pos-2) (xs ++ [false,false]))
    (hmark : t mark=true) (hz1 : t (mark+1)=false) (hz2 : t (mark+2)=false)
    (right : Holds t (mark+3) (ys ++ [false,false,false])) :
    let u := setAt (mark+2) (clearAt mark t)
    let out := setAt pos u
    out pos=true ∧ (∀ q, mark+2<q → q≠pos → out q=t q) ∧
      silentSegment machine (cfg 262 (pos-2) t) (cfg 25 (pos-1) out) (2*xs.length+9) := by
  dsimp only
  let u0 := clearAt mark t
  let u := setAt (mark+2) u0
  let out := setAt pos u
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
  have htail := holds_append_tail t (mark+3) ys [false,false,false] right
  have hp : mark+3+(ys.length : Int)=pos-1 := by omega
  rw [hp] at htail
  simp only [Holds] at htail
  have hzpos : t pos=false := by
    have he : pos-1+1=pos := by omega
    simpa only [he] using htail.2.1
  have hznext : t (pos+1)=false := by
    have he : pos-1+1+1=pos+1 := by omega
    simpa only [he] using htail.2.2.1
  have hprefix : Holds t (mark+3) (ys ++ [false,false]) := by
    apply holds_prefix_word t (mark+3) (ys ++ [false,false]) [false]
    simpa [List.append_assoc] using right
  have huword : Holds u (mark+3) (ys ++ [false,false]) := by
    apply holds_transport t u (mark+3) _ hprefix
    intro q hq _
    have hne1 : q≠mark := by omega
    have hne2 : q≠mark+2 := by omega
    simp [u,u0,setAt,clearAt,hne1,hne2]
  have hforward := scan268 ys hy (mark+3) u huword
  have hforward' : silentSegment machine (cfg 268 (mark+3) u) (cfg 17 (pos+1) u)
      (ys.length+2) := by
    have he : mark+3+(ys.length : Int)+2=pos+1 := by omega
    simpa only [he] using hforward
  have hupos : u pos=false := by
    have he : mark+2<pos := by omega
    simp [u,u0,setAt,clearAt,show pos≠mark+2 by omega,show pos≠mark by omega,hzpos]
  have hunext : u (pos+1)=false := by
    simp [u,u0,setAt,clearAt,show pos+1≠mark+2 by omega,show pos+1≠mark by omega,hznext]
  have d := oneSeg machine _ _ (step17_zero (pos+1) u hunext)
  have d' : silentSegment machine (cfg 17 (pos+1) u) (cfg 13 pos u) 1 := by
    have he : pos+1-1=pos := by omega
    simpa only [he] using d
  have e := oneSeg machine _ _ (step13_zero pos u hupos)
  have de := segAdd machine _ _ _ 1 1 d' e
  have first := segAdd machine _ _ _ (xs.length+2) 3 hleft' abc'
  have middle := segAdd machine _ _ _ (xs.length+2+3) (ys.length+2) first hforward'
  have all := segAdd machine _ _ _ (xs.length+2+3+(ys.length+2)) 2 middle de
  have htime : xs.length+2+3+(ys.length+2)+2=2*xs.length+9 := by omega
  rw [htime] at all
  refine ⟨?_,?_,?_⟩
  · simp [out,setAt]
  · intro q hq hne
    have hn1 : q≠mark := by omega
    have hn2 : q≠mark+2 := by omega
    simp [out,u,u0,setAt,clearAt,hne,hn1,hn2]
  · simpa only [out,u,u0] using all

#print axioms restore_zero
#print axioms scan262
#print axioms scan268
end Shared.Beeping.NPcoNP.NativeZeroRestore
