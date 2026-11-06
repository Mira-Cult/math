import Shared.Beeping.NPcoNP.NativeHalfEntryTo28
import Shared.Beeping.NPcoNP.NativeHalfProtectedMarker
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact
import Shared.Beeping.NPcoNP.NativeHalfCarryTo93
import Shared.Beeping.NPcoNP.NativeHalfBankFirst

/-! Carry-marker progress from the prepared selected native-HALF entry
through the literal state-83 and state-93 selector scans. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryTo93

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryTo28
open Shared.Beeping.NPcoNP.NativeHalfState1Canonical
open Shared.Beeping.NPcoNP.NativeHalfProtectedMarker
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfCarryTo93
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- From a supplied selected entry, the literal table reaches state 83 in
positive finite silent time, retaining the marker made by its carry and the
prefix strictly to its left. -/
theorem selected_entry_to83 (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
    ∃ (n : Nat) (p : Int) (e : Config 284), 0<n ∧ e.state=83 ∧ e.head=p-1 ∧
      (∃ (head : Int) (k : Nat) (t : Int → Bool) (stop : Int), p=head-(k : Int) ∧
        (value%2=1 → head=ctrl-1) ∧ (value%2=0 → head≤ctrl-2) ∧
        (value%2=0 → back (head+1)=false) ∧
        (value%2=0 → ∀ p, head+1<p → p<ctrl → back p=true) ∧
        downHolds back head (List.replicate k true ++ [false]) ∧
        Holds t (ctrl+2) (encode values) ∧
        t=state1Tape back ctrl head values ∧
        (∀ q≤head, t q=back q) ∧ stop=ctrl+2+((values.headD 0 : Nat) : Int) ∧
        (∀ q, ctrl+3+((values.headD 0 : Nat) : Int)≤q → e.tape q=t q) ∧
        (∃ tail, values=(values.headD 0)::tail ∧
          Holds e.tape (ctrl+2) (List.replicate (values.headD 0) false ++ [true,false]) ∧
          Holds e.tape (ctrl+4+((values.headD 0 : Nat) : Int)) (encode tail)) ∧
        e.tape=put (clearRange (put (result t head k) (ctrl+2) false) (ctrl+3) (stop+1)) stop true) ∧
      e.tape p=true ∧ e.tape (e.head+1)=true ∧
      (∀ q<p, e.tape q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right)) e n := by
  dsimp only
  obtain ⟨n,k,head,t,hn,hodd,heven,hstopBack,honesBack,hcorr,hbank,hcanonical,hreserve,hprefix,hcarry,hfirst⟩ :=
    selected_entry_to28 back ctrl z value left right hz
  have hlt : head<ctrl := by
    by_cases hv : value%2=0
    · have hh := heven hv
      omega
    · have hv' : value%2=1 := by omega
      have hh := hodd hv'
      omega
  let p := head-(k : Int)
  let t' := put (result t head k) (ctrl+2) false
  let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
  have hp : p≤(ctrl+3)-2 := by dsimp [p]; omega
  have hmark : t' p=true := by
    have hn : p≠ctrl+2 := by dsimp [p]; omega
    dsimp [t']
    rw [put_other _ _ _ _ hn]
    simp [result,put,p]
  have hleft : t' ((ctrl+3)-1)=false := by
    have he : ctrl+3-1=ctrl+2 := by omega
    rw [he]
    simp [t',put]
  have hright : t' ((ctrl+3)+((encode values).length : Int))=false := by
    let q := (ctrl+3)+((encode values).length : Int)
    have hne : q≠ctrl+2 := by dsimp [q]; omega
    have hne' : q≠head-(k : Int) := by dsimp [q]; omega
    have hout : ¬ (head-(k : Int)<q ∧ q≤head) := by dsimp [q]; omega
    change put (result t head k) (ctrl+2) false q=false
    rw [put_other _ _ _ _ hne]
    change (if q=head-(k : Int) then true else
      if head-(k : Int)<q ∧ q≤head then false else t q)=false
    rw [if_neg hne',if_neg hout]
    exact hreserve
  have hcorridor : ∀ q, p<q → q<ctrl+3 → t' q=false := by
    intro q hq hq'
    by_cases hq2 : q=ctrl+2
    · subst q
      simp [t',put]
    · have hne : q≠head-(k : Int) := by dsimp [p] at hq; omega
      change put (result t head k) (ctrl+2) false q=false
      rw [put_other _ _ _ _ hq2]
      change (if q=head-(k : Int) then true else
        if head-(k : Int)<q ∧ q≤head then false else t q)=false
      rw [if_neg hne]
      by_cases hqhead : q≤head
      · rw [if_pos (by dsimp [p] at hq; omega)]
      · rw [if_neg (by omega)]
        exact hcorr q (by omega) (by omega)
  obtain ⟨m,stop,out,hm,hstop,hprotected,hstopzero,hstopones,hexact,heprefix,hsecond⟩ :=
    state28_to83_exact (ctrl+3) p t' hp hmark hcorridor (encode values).length hright
  have hvne : values≠[] := by dsimp [values]; simp
  obtain ⟨v,vs,hvals⟩ := List.exists_cons_of_ne_nil hvne
  have hvfirst : values.headD 0=v := by rw [hvals]; rfl
  have hbv : Holds t (ctrl+2) (encode (v::vs)) := by
    change Holds t (ctrl+2) (encode values) at hbank
    rw [hvals] at hbank
    exact hbank
  obtain ⟨hones,hzero⟩ := first_block_cells t (ctrl+2) v vs hbv
  have hrightPres : ∀ q, ctrl+3≤q → t' q=t q := by
    intro q hq
    have hne : q≠ctrl+2 := by omega
    have hne' : q≠head-(k : Int) := by omega
    have hout : ¬ (head-(k : Int)<q ∧ q≤head) := by omega
    change put (result t head k) (ctrl+2) false q=t q
    rw [put_other _ _ _ _ hne]
    change (if q=head-(k : Int) then true else
      if head-(k : Int)<q ∧ q≤head then false else t q)=t q
    rw [if_neg hne',if_neg hout]
  have hrun : ∀ q, ctrl+3≤q → q≤ctrl+2+(v : Int) → t' q=true := by
    intro q hq hq'
    let i := (q-(ctrl+2)).toNat
    have hi : (i : Int)=q-(ctrl+2) := Int.toNat_of_nonneg (by omega)
    have hiv : i≤v := by omega
    rw [hrightPres q hq]
    have hh := hones i hiv
    have he : ctrl+2+(i : Int)=q := by omega
    rwa [he] at hh
  have hdelimiter : t' (ctrl+3+(v : Int))=false := by
    rw [hrightPres _ (by omega)]
    have he : ctrl+2+((v+1 : Nat) : Int)=ctrl+3+(v : Int) := by push_cast; omega
    rw [he] at hzero
    exact hzero
  have hstopExact : stop=ctrl+2+(v : Int) := by
    by_contra hn
    by_cases hl : stop<ctrl+2+(v : Int)
    · have ht := hrun (stop+1) (by omega) (by omega)
      rw [hstopzero] at ht
      contradiction
    · have ht := hstopones (ctrl+3+(v : Int)) (by omega) (by omega)
      rw [hdelimiter] at ht
      contradiction
  have hstopFirst : stop=ctrl+2+((values.headD 0 : Nat) : Int) := by rw [hvfirst]; exact hstopExact
  have hrightFrame : ∀ q, ctrl+3+((values.headD 0 : Nat) : Int)≤q → out q=t q := by
    intro q hq
    have hq' : stop+1≤q := by rw [hstopFirst,hvfirst] at *; omega
    rw [hexact,put_other _ _ _ _ (by omega)]
    change (if ctrl+3≤q ∧ q<stop+1 then false else t' q)=t q
    rw [if_neg (by omega)]
    exact hrightPres q (by rw [hvfirst] at hq; omega)
  have hfirstZeros : ∀ i : Nat, i<v → out (ctrl+2+(i : Int))=false := by
    intro i hi
    let q := ctrl+2+(i : Int)
    have hne : q≠stop := by dsimp [q]; omega
    rw [hexact,put_other _ _ _ _ hne]
    change (if ctrl+3≤q ∧ q<stop+1 then false else t' q)=false
    by_cases hi0 : i=0
    · subst i
      have hq : q=ctrl+2 := by dsimp [q]; simp
      rw [if_neg (by omega),hq]
      simp [t',put]
    · rw [if_pos (by dsimp [q]; omega)]
  have hfirstMark : out (ctrl+2+(v : Int))=true := by
    rw [← hstopExact,hexact]
    simp [put]
  have hfirstDelimiter : out (ctrl+3+(v : Int))=false := by
    have hq : ctrl+3+((values.headD 0 : Nat) : Int)≤ctrl+3+(v : Int) := by rw [hvfirst]
    rw [hrightFrame _ hq]
    have he : ctrl+2+((v+1 : Nat) : Int)=ctrl+3+(v : Int) := by push_cast; omega
    rwa [he] at hzero
  have hfirstZerosWord : Holds out (ctrl+2) (List.replicate v false) := by
    apply holds_of_get
    intro i hi
    have hi' : i<v := by simpa using hi
    have hh := hfirstZeros i hi'
    simpa using hh
  have hpair : Holds out ((ctrl+2)+((List.replicate v false).length : Int)) [true,false] := by
    simp only [List.length_replicate,Holds]
    constructor
    · exact hfirstMark
    · have he : ctrl+2+(v : Int)+1=ctrl+3+(v : Int) := by omega
      rw [he]
      exact ⟨hfirstDelimiter,trivial⟩
  have hfirstBlock := holds_append out (ctrl+2) (List.replicate v false) [true,false] hfirstZerosWord hpair
  have htailT := first_block_tail t (ctrl+2) v vs hbv
  have htailOut : Holds out (ctrl+4+(v : Int)) (encode vs) := by
    apply holds_transport t out _ (encode vs) ?_ ?_
    · have he : ctrl+2+((v+2 : Nat) : Int)=ctrl+4+(v : Int) := by push_cast; omega
      rwa [he] at htailT
    · intro q hq hq'
      symm
      apply hrightFrame
      rw [hvfirst]
      omega
  have hphysicalBank : ∃ tail, values=(values.headD 0)::tail ∧
      Holds out (ctrl+2) (List.replicate (values.headD 0) false ++ [true,false]) ∧
      Holds out (ctrl+4+((values.headD 0 : Nat) : Int)) (encode tail) := by
    refine ⟨vs,?_,?_,?_⟩
    · rw [hvfirst]; exact hvals
    · rw [hvfirst]; exact hfirstBlock
    · rw [hvfirst]; exact htailOut
  have hback : ∀ q<p, out q=back q := by
    intro q hq
    rw [heprefix q (by dsimp [p] at hq; omega)]
    have hne : q≠ctrl+2 := by dsimp [p] at hq; omega
    have hne' : q≠head-(k : Int) := by dsimp [p] at hq; omega
    have hout : ¬ (head-(k : Int)<q ∧ q≤head) := by dsimp [p] at hq; omega
    change put (result t head k) (ctrl+2) false q=back q
    rw [put_other _ _ _ _ hne]
    change (if q=head-(k : Int) then true else
      if head-(k : Int)<q ∧ q≤head then false else t q)=back q
    rw [if_neg hne',if_neg hout]
    exact hprefix q (by dsimp [p] at hq; omega)
  refine ⟨n+m,p,cfg 83 (p-1) out,by omega,rfl,rfl,⟨head,k,t,stop,rfl,hodd,heven,hstopBack,honesBack,hcarry,hbank,hcanonical,hprefix,hstopFirst,hrightFrame,hphysicalBank,hexact⟩,hprotected,?_,hback,?_⟩
  · simpa [cfg] using hprotected
  · exact segAdd machine _ _ _ n m hfirst hsecond

/-- Every supplied selected entry reaches state 93 silently after finitely
many paid transitions. Its carry marker and lower original prefix survive. -/
theorem selected_entry_to93 (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    ∃ (n : Nat) (p : Int) (e : Config 284), 0<n ∧ e.state=93 ∧
      e.tape p=true ∧ (∀ q<p, e.tape q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right)) e n := by
  dsimp only
  obtain ⟨m,p,c,hm,hstate,hhead,hcarry,hmarker,hfound,hprefix,hseg⟩ :=
    selected_entry_to83 back ctrl z value left right hz
  have htail : ∀ q≤min z (p-1), c.tape q=false := by
    intro q hq
    have hzq : q≤z := le_trans hq (min_le_left _ _)
    have hpq : q<p := by have := le_trans hq (min_le_right z (p-1)); omega
    rw [hprefix q hpq]
    exact hz q hzq
  obtain ⟨n,e,hn,hstate',htape,hcont⟩ :=
    state83_to_93 c.head (min z (p-1)) c.tape htail hfound
  have hcfg : c=cfg 83 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hstate] using he
  have hseg' : silentSegment machine c e n := by simpa [← hcfg] using hcont
  refine ⟨m+n,p,e,by omega,hstate',?_,?_,?_⟩
  · rw [htape]; exact hmarker
  · intro q hq; rw [htape]; exact hprefix q hq
  · exact segAdd machine _ _ _ m n hseg hseg'

end Shared.Beeping.NPcoNP.NativeHalfEntryTo93

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryTo93.selected_entry_to83
#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryTo93.selected_entry_to93
