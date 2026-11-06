import Shared.Beeping.NPcoNP.NativeFirstZeroCycle

/-! The selector pass after the first zero-branch fill. Its exact finite
behavior is proved for a supplied tape window; graph-level recurrence remains
an independent obligation. -/
namespace Shared.Beeping.NPcoNP.NativeFirstZeroNext
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstZeroOperation
open Shared.Beeping.NPcoNP.NativeFirstZeroCycle
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

theorem down_ones (n : Nat) (a : Int) (t : Int → Bool) (rest : List Bool)
    (ones : ∀ i : Nat, i<n → t (a-(i : Int))=true)
    (tail : downHolds t (a-(n : Int)) rest) :
    downHolds t a (List.replicate n true ++ rest) := by
  induction n generalizing a with
  | zero => simpa using tail
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,downHolds]
    refine ⟨?_,?_⟩
    · simpa using ones 0 (by omega)
    · apply ih (a-1)
      · intro i hi
        have he : (a-1)-(i : Int)=a-((i+1 : Nat) : Int) := by push_cast; omega
        rw [he]
        exact ones (i+1) (by omega)
      · have he : (a-1)-(n : Int)=a-((Nat.succ n : Nat) : Int) := by push_cast; omega
        simpa only [he] using tail

theorem chain82 : Chain 13 82 92 := by
  apply Chain.cons ScanRow.r82
  apply Chain.cons ScanRow.r81
  apply Chain.cons ScanRow.r80
  apply Chain.cons ScanRow.r91
  apply Chain.cons ScanRow.r90
  apply Chain.cons ScanRow.r89
  apply Chain.cons ScanRow.r88
  apply Chain.cons ScanRow.r87
  apply Chain.cons ScanRow.r86
  apply Chain.cons ScanRow.r85
  apply Chain.cons ScanRow.r84
  apply Chain.cons ScanRow.r79
  apply Chain.cons ScanRow.r78
  exact Chain.refl _

/-- After the fill, state 83 scans the filled run and returns to state 93.
The run may be empty; `r` is its length up to the state-83 starting head. -/
theorem second_selector (h : Int) (r : Nat) (t : Int → Bool)
    (left : ∀ q, q<h-4 → t q=false)
    (h4 : t (h-4)=true) (h3 : t (h-3)=true) (h2 : t (h-2)=false)
    (h1 : t (h-1)=true) (h0 : t h=false) (p1 : t (h+1)=false)
    (p2 : t (h+2)=true) (p3 : t (h+3)=false) (p4 : t (h+4)=false)
    (run : ∀ q, h+5≤q → q≤h+4+(r : Int) → t q=true) :
    silentSegment machine (cfg 83 (h+4+(r : Int)) t) (cfg 93 (h-3) t) (r+29) := by
  let ks : List Nat := [0,1,0,1,2] ++ List.replicate 8 0
  have htail : downHolds t (h+3) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact p3 | (convert p2 using 1 <;> congr 1 <;> omega) |
      (convert p1 using 1 <;> congr 1 <;> omega) |
      (convert h0 using 1 <;> congr 1 <;> omega) |
      (convert h1 using 1 <;> congr 1 <;> omega) |
      (convert h2 using 1 <;> congr 1 <;> omega) |
      (convert h3 using 1 <;> congr 1 <;> omega) |
      (convert h4 using 1 <;> congr 1 <;> omega) | (apply left; omega)
  have hfirst : downHolds t (h+4+(r : Int)) (List.replicate r true ++ false :: (blocks ks ++ [])) := by
    apply down_ones
    · intro i hi
      apply run <;> omega
    · have he : h+4+(r : Int)-(r : Int)=h+4 := by omega
      rw [he]
      change t (h+4)=false ∧ downHolds t (h+4-1) (blocks ks ++ [])
      have hs : h+4-1=h+3 := by omega
      exact ⟨p4,by simpa only [hs] using htail⟩
  have hs1 := (scan_block ScanRow.r83 r (h+4+(r : Int)) t (blocks ks ++ []) hfirst).2
  have hs1' : silentSegment machine (cfg 83 (h+4+(r : Int)) t) (cfg 82 (h+3) t) (r+1) := by
    have he : h+4+(r : Int)-((r+1 : Nat) : Int)=h+3 := by push_cast; omega
    simpa only [he] using hs1
  have hs2 := (chain_blocks chain82 ks (h+3) t [] (by decide) htail).2
  have hs2' : silentSegment machine (cfg 82 (h+3) t) (cfg 92 (h-14) t) 17 := by
    have he : h+3-17=h-14 := by omega
    simpa [ks,blocks,List.replicate_succ,he] using hs2
  have hz : ∀ i : Nat, i<10 → t ((h-14)+(i : Int))=false := by
    intro i hi
    apply left
    omega
  have ho : t ((h-14)+(10 : Int))=true := by
    have he : h-14+10=h-4 := by omega
    simpa only [he] using h4
  have hs3 := scan92_exact 10 (h-14) t hz ho
  have hs12 := segAdd machine _ _ _ (r+1) 17 hs1' hs2'
  have all := segAdd machine _ _ _ (r+1+17) 11 hs12 hs3
  convert all using 1 <;> congr 1 <;> omega

theorem row62_one : machine.table.row 62 true = ⟨true,.right,279,false⟩ := by decide

theorem step62_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 62 h t)=(cfg 279 (h+1) t,false) := by
  have hw : (⟨62,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row62_one,Move.apply,hw]

/-- The second pass follows the same three dispatch rows, but the newly
set bit selects state 279 at the next branch. -/
theorem dispatch_to279 (h : Int) (t : Int → Bool)
    (h3 : t (h-3)=true) (h2 : t (h-2)=false) (h1 : t (h-1)=true)
    (h0 : t h=false) (p1 : t (h+1)=false) (p2 : t (h+2)=true) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 279 (h+3) t) 6 := by
  have s0 := dispatch_93_to166 h t h3 h2 h1
  have s1 := oneSeg machine _ _ (step166_zero h t h0)
  have s2 := oneSeg machine _ _ (step100_zero (h+1) t p1)
  have s3 := oneSeg machine _ _ (step62_one (h+2) t p2)
  have a := segAdd machine _ _ _ 3 1 s0 s1
  have b := segAdd machine _ _ _ 4 1 a s2
  have b' : silentSegment machine (cfg 93 (h-3) t) (cfg 62 (h+2) t) 5 := by
    simpa [Int.add_assoc] using b
  have c := segAdd machine _ _ _ 5 1 b' s3
  simpa [Int.add_assoc] using c

/-- From the supplied flagged layout, the carry, first dispatch, zero fill,
and a second selector pass reach literal state 279 with exactly one event.
The suffix beginning at the supplied separator remains unchanged. -/
theorem supplied_beep_to279_full (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q≤h+6 → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsep : h+3<separator) (hsepzero : t separator=false) :
    ∃ (n : Nat) (mid : Int → Bool) (stop : Int), 1<n ∧
      h+6≤stop ∧ stop<separator ∧ t (stop+1)=false ∧ mid stop=true ∧
      Holds mid (h-4) [true,true,false,true,false,false] ∧
      (∀ q, q<h-4 → mid q=false) ∧
      (∀ q, h≤q → q<stop → mid q=false) ∧
      (∀ q, separator≤q → fillRange (setAt (h+2) mid) (h+5) stop q=t q) ∧
      physical.advance (cfg 99 h t) n=
        cfg 279 (h+3) (fillRange (setAt (h+2) mid) (h+5) stop) ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,stop,hn,hstop,hsep',hstopNext,hmark,hword,hleft,hclear,hframe,ha,hw⟩ :=
    supplied_beep_zero_cycle_detail h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2 ones left
      hb right hsep hsepzero
  let out := fillRange (setAt (h+2) mid) (h+5) stop
  let r := (stop-(h+6)).toNat
  have hr : (r : Int)=stop-(h+6) := Int.toNat_of_nonneg (by omega)
  have he : stop=h+6+(r : Int) := by omega
  have frame : ∀ q, q<h+5 → q≠h+2 → out q=mid q := by
    intro q hq hnq
    have hno : ¬ (h+5≤q ∧ q<stop) := by omega
    simp [out,fillRange,setAt,hno,hnq]
  have h4m : mid (h-4)=true := by
    have hv := hword
    simp only [Holds] at hv
    exact hv.1
  have h3m : mid (h-3)=true := by
    have hv := hword
    simp only [Holds] at hv
    have hp : h-4+1=h-3 := by omega
    simpa only [hp] using hv.2.1
  have h2m : mid (h-2)=false := by
    have hv := hword
    simp only [Holds] at hv
    have hp : h-4+1+1=h-2 := by omega
    simpa only [hp] using hv.2.2.1
  have h1m : mid (h-1)=true := by
    have hv := hword
    simp only [Holds] at hv
    have hp : h-4+1+1+1=h-1 := by omega
    simpa only [hp] using hv.2.2.2.1
  have l : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [frame q (by omega) (by omega)]
    exact hleft q hq
  have h4 : out (h-4)=true := by rw [frame _ (by omega) (by omega)]; exact h4m
  have h3 : out (h-3)=true := by rw [frame _ (by omega) (by omega)]; exact h3m
  have h2 : out (h-2)=false := by rw [frame _ (by omega) (by omega)]; exact h2m
  have h1 : out (h-1)=true := by rw [frame _ (by omega) (by omega)]; exact h1m
  have h0 : out h=false := by rw [frame _ (by omega) (by omega)]; exact hclear h (by omega) (by omega)
  have p1 : out (h+1)=false := by rw [frame _ (by omega) (by omega)]; exact hclear _ (by omega) (by omega)
  have p2 : out (h+2)=true := by
    simp [out,fillRange,setAt]
  have p3 : out (h+3)=false := by rw [frame _ (by omega) (by omega)]; exact hclear _ (by omega) (by omega)
  have p4 : out (h+4)=false := by rw [frame _ (by omega) (by omega)]; exact hclear _ (by omega) (by omega)
  have run : ∀ q, h+5≤q → q≤h+4+(r : Int) → out q=true := by
    intro q hq hq'
    have hy : h+5≤q ∧ q<stop := by omega
    simp [out,fillRange,hy]
  have hselector := second_selector h r out l h4 h3 h2 h1 h0 p1 p2 p3 p4 run
  have hselector' : silentSegment machine (cfg 83 (stop-2) out) (cfg 93 (h-3) out) (r+29) := by
    have hp : stop-2=h+4+(r : Int) := by omega
    simpa only [hp] using hselector
  have hnext := dispatch_to279 h out h3 h2 h1 h0 p1 p2
  have hseg := segAdd machine _ _ _ (r+29) 6 hselector' hnext
  have ha' : physical.advance (cfg 99 h t) n=cfg 83 (stop-2) out := by simpa [out] using ha
  obtain ⟨ha'',hw''⟩ := append_silent _ _ _ n (r+29+6) ha' hw hseg
  exact ⟨n+(r+29+6),mid,stop,by omega,hstop,hsep',hstopNext,hmark,hword,hleft,hclear,hframe,ha'',hw''⟩

/-- The established detail interface follows by forgetting the protected
control word and left-blank frame. -/
theorem supplied_beep_to279_detail (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q≤h+6 → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsep : h+3<separator) (hsepzero : t separator=false) :
    ∃ (n : Nat) (mid : Int → Bool) (stop : Int), 1<n ∧
      h+6≤stop ∧ stop<separator ∧ t (stop+1)=false ∧ mid stop=true ∧
      (∀ q, h≤q → q<stop → mid q=false) ∧
      (∀ q, separator≤q → fillRange (setAt (h+2) mid) (h+5) stop q=t q) ∧
      physical.advance (cfg 99 h t) n=
        cfg 279 (h+3) (fillRange (setAt (h+2) mid) (h+5) stop) ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,stop,hn,hs,hsep',hnext,hm,_hw,_hl,hc,hf,ha,he⟩ :=
    supplied_beep_to279_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2 ones left
      hb right hsep hsepzero
  exact ⟨n,mid,stop,hn,hs,hsep',hnext,hm,hc,hf,ha,he⟩

/-- The original first-branch interface follows from the detailed tape form. -/
theorem supplied_beep_to279 (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q≤h+6 → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsep : h+3<separator) (hsepzero : t separator=false) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      (∀ q, separator≤q → out q=t q) ∧
      physical.advance (cfg 99 h t) n=cfg 279 (h+3) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,stop,hn,_hs,_hsep,_hnext,_hm,_hc,hf,ha,hw⟩ :=
    supplied_beep_to279_detail h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2 ones left
      hb right hsep hsepzero
  exact ⟨n,fillRange (setAt (h+2) mid) (h+5) stop,hn,hf,ha,hw⟩

#print axioms down_ones
#print axioms second_selector
#print axioms dispatch_to279
#print axioms supplied_beep_to279_full
#print axioms supplied_beep_to279_detail
#print axioms supplied_beep_to279
end Shared.Beeping.NPcoNP.NativeFirstZeroNext
