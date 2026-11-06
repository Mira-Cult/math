import Shared.Beeping.NPcoNP.Native280ZeroRestore
import Shared.Beeping.NPcoNP.Native280Positive
import Shared.Beeping.NPcoNP.NativeRow10Array

/-! Both supplied row-10 bank-operation branches in producer-array order. -/
namespace Shared.Beeping.NPcoNP.NativeRow10Operation
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native280ZeroRestore
open Shared.Beeping.NPcoNP.Native280Positive
open Shared.Beeping.NPcoNP.NativeRow10Array
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- A zero target is restored unchanged and the actual graph row selects 11.
The physical segment stops at state 25; its return is a separate obligation. -/
theorem zero_operation_full (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ (0::graphTail))
    (hlong : h+12≤separator) (mark : t (h+8)=true)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode (0::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    let pos := separator+1+((encode values).length : Int)
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=11 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧
      Holds out (separator+1)
        (encode (arrayBank result.bank) ++ (encode more ++ [false,false])) ∧
      (∀ q, separator≤q → out q=t q) ∧
      (∀ q, q<h+8 → out q=t q) ∧ out (h+8)=false ∧ out (h+9)=false ∧
      out (h+10)=true ∧ (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 25 (pos-1) out) k := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  let out := setAt pos (setAt (h+10) (clearAt (h+8) (clearAt pos t)))
  have hw : Holds t (separator+1)
      (encode values ++ (block 0 ++ (encode (graphTail++more) ++ [false,false]))) := by
    simpa [encode,List.append_assoc] using word
  have hz := zero_touch_restore_280 (h+6) separator t values (encode (graphTail++more) ++ [false,false])
    hlen (by omega) (by simpa only [show h+6+2=h+8 by omega] using mark)
    (by simpa only [show h+6+3=h+9 by omega] using h9)
    (by simpa only [show h+6+4=h+10 by omega] using h10)
    (by intro q hq hq'; exact ones q (by omega) hq') sep hw
  have hframe : ∀ q, separator≤q → out q=t q := by
    simpa only [show h+6+2=h+8 by omega,show h+6+4=h+10 by omega,pos,out] using hz.1
  let duration := (separator-(h+6+5)).toNat+(encode values).length+5+
    (2*(unaryBankPrefix (separator-(h+6+6)).toNat values).reverse.length+9)
  have hseg : ∃ k : Nat, 0<k ∧ silentSegment machine (cfg 280 (h+9) t) (cfg 25 (pos-1) out) k := by
    refine ⟨duration,by dsimp [duration]; omega,?_⟩
    simpa only [show h+6+3=h+9 by omega,show h+6+2=h+8 by omega,
      show h+6+4=h+10 by omega,pos,out,duration] using hz.2.2.2.2
  obtain ⟨k,hk,hseg'⟩ := hseg
  have hr := row10_array bank values 0 graphTail hlen hgraph
  simp only [if_pos rfl] at hr
  have hbank : Holds out (separator+1)
      (encode values ++ (encode (0::(graphTail++more)) ++ [false,false])) := by
    apply holds_transport t out _ _ word
    intro q hq _
    exact (hframe q (by omega)).symm
  have hbank' : Holds out (separator+1)
      (encode (arrayBank (target.system.step ⟨10,bank⟩).1.bank) ++ (encode more ++ [false,false])) := by
    rw [hr.2.2]
    simpa [encode_append,encode,List.append_assoc] using hbank
  have hbefore : ∀ q, q<h+8 → out q=t q := by
    simpa only [show h+6+2=h+8 by omega,show h+6+4=h+10 by omega,pos,out] using hz.2.1
  have hz8 : out (h+8)=false := by
    simpa only [show h+6+2=h+8 by omega,show h+6+4=h+10 by omega,pos,out] using hz.2.2.1
  have ho10 : out (h+10)=true := by
    simpa only [show h+6+2=h+8 by omega,show h+6+4=h+10 by omega,pos,out] using hz.2.2.2.1
  have hz9 : out (h+9)=false := by
    simp [out,setAt,clearAt,show h+9≠pos by dsimp [pos]; omega,
      show h+9≠h+10 by omega,show h+9≠h+8 by omega,h9]
  have hc : ∀ q, h+11≤q → q<separator → out q=true := by
    intro q hq hq'
    simp [out,setAt,clearAt,show q≠pos by dsimp [pos]; omega,
      show q≠h+10 by omega,show q≠h+8 by omega,ones q hq hq']
  have hs : out separator=false := by rw [hframe separator (by omega)]; exact sep
  exact ⟨k,out,hk,hr.2.1,hr.1,hbank',hframe,hbefore,hz8,hz9,ho10,hc,hs,hseg'⟩

theorem zero_operation (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ (0::graphTail))
    (hlong : h+12≤separator) (mark : t (h+8)=true)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode (0::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    let pos := separator+1+((encode values).length : Int)
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=11 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧
      Holds out (separator+1)
        (encode (arrayBank result.bank) ++ (encode more ++ [false,false])) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 25 (pos-1) out) k := by
  obtain ⟨k,out,hk,hs,he,hbank,hframe,_,_,_,_,_,_,hseg⟩ :=
    zero_operation_full h separator t values graphTail more bank hlen hgraph hlong mark h9 h10 ones sep word
  exact ⟨k,out,hk,hs,he,hbank,hframe,hseg⟩

/-- The rightmost bank cell changed by the positive row-10 operation. -/
def positiveFrontier (separator : Int) (values : List Nat) (v : Nat)
    (graphTail more : List Nat) : Int :=
  separator+1+((encode values).length : Int)+2+
    ((List.replicate v true ++ (graphTail++more).flatMap
      (fun z => false :: List.replicate (z+1) true)).length : Int)

/-- A positive target is decremented and the actual graph row loops to 10.
The physical segment stops at state 23; its return is a separate obligation. -/
theorem positive_operation_full (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (v : Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ ((v+1)::graphTail))
    (hlong : h+12≤separator) (mark : t (h+8)=true)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    let pos := separator+1+((encode values).length : Int)
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=10 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧
      Holds out (separator+1)
        (encode (arrayBank result.bank) ++ (encode more ++ [true,false,false])) ∧
      (∀ q, positiveFrontier separator values v graphTail more<q → out q=t q) ∧
      (∀ q, q<h+8 → out q=t q) ∧ out (h+8)=false ∧ out (h+9)=false ∧
      out (h+10)=true ∧ (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 23 (pos-2) out) k := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  let ys := unaryBankPrefix (separator-(h+12)).toNat values
  let original := setAt pos (setAt (h+10) (clearAt (h+8) (clearAt pos t)))
  let suffix := List.replicate v true ++ (graphTail++more).flatMap (fun z => false :: List.replicate (z+1) true)
  let f := pos+2+(suffix.length : Int)
  let out := Shared.Beeping.NPcoNP.NativeHalfSweep.spec original f (suffix.length+2)
  have hp := positive_touch_shift_280 (h+6) separator t values v (graphTail++more) hlen
    (by omega) (by simpa only [show h+6+2=h+8 by omega] using mark)
    (by simpa only [show h+6+3=h+9 by omega] using h9)
    (by simpa only [show h+6+4=h+10 by omega] using h10)
    (by intro q hq hq'; exact ones q (by omega) hq') sep word
  have htarget : Holds out pos (encode (v::(graphTail++more)) ++ [true,false,false]) := by
    simpa only [show h+6+2=h+8 by omega,show h+6+4=h+10 by omega,pos,original,suffix,f,out] using hp.1
  have hframe : ∀ q, separator≤q → q<pos → out q=t q := by
    intro q hq hq'
    have hf := hp.2.2.1 q hq (Or.inl hq')
    simpa only [show h+6+2=h+8 by omega,show h+6+4=h+10 by omega,pos,original,suffix,f,out] using hf
  have hrightframe : ∀ q, positiveFrontier separator values v graphTail more<q → out q=t q := by
    intro q hq
    have hq' : f<q := by simpa [positiveFrontier,pos,suffix,f] using hq
    have hf := hp.2.2.1 q (by dsimp [f,pos] at hq'; omega) (Or.inr hq')
    simpa only [show h+6+2=h+8 by omega,show h+6+4=h+10 by omega,pos,original,suffix,f,out] using hf
  have hpref : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) (encode values) _ word
  have hpref' : Holds out (separator+1) (encode values) := by
    apply holds_transport t out _ _ hpref
    intro q hq hq'
    exact (hframe q (by omega) (by dsimp [pos]; omega)).symm
  have hcombined := holds_append_intro out (separator+1) (encode values)
    (encode (v::(graphTail++more)) ++ [true,false,false]) hpref' (by simpa only [pos] using htarget)
  have hr := row10_array bank values (v+1) graphTail hlen hgraph
  have hnonzero : v+1≠0 := by omega
  simp only [hnonzero,if_false,Nat.add_sub_cancel_right] at hr
  have hbank : Holds out (separator+1)
      (encode (arrayBank (target.system.step ⟨10,bank⟩).1.bank) ++ (encode more ++ [true,false,false])) := by
    rw [hr.2.2]
    simpa [encode_append,encode,List.append_assoc] using hcombined
  let duration := (separator-(h+6+5)).toNat+(encode values).length+5+
    (2*ys.reverse.length+7)+(2*suffix.length+7)
  have hseg : ∃ k : Nat, 0<k ∧ silentSegment machine (cfg 280 (h+9) t) (cfg 23 (pos-2) out) k := by
    refine ⟨duration,by dsimp [duration]; omega,?_⟩
    simpa only [show h+6+2=h+8 by omega,show h+6+3=h+9 by omega,
      show h+6+4=h+10 by omega,show h+6+6=h+12 by omega,pos,ys,original,suffix,f,out,duration] using hp.2.2.2
  obtain ⟨k,hk,hseg'⟩ := hseg
  have hbefore : ∀ q, q<pos → out q=original q := by
    intro q hq
    have hne : q≠f := by dsimp [f]; omega
    have hn : ¬ (f-((suffix.length+2 : Nat):Int)≤q ∧ q<f) := by
      dsimp [f]
      push_cast
      omega
    change (if q=f then true else if f-((suffix.length+2 : Nat):Int)≤q ∧ q<f
      then original (q+1) else original q)=original q
    rw [if_neg hne,if_neg hn]
  have hleft : ∀ q, q<h+8 → out q=t q := by
    intro q hq
    rw [hbefore q (by dsimp [pos]; omega)]
    simp [original,setAt,clearAt,show q≠pos by dsimp [pos]; omega,
      show q≠h+10 by omega,show q≠h+8 by omega]
  have hz8 : out (h+8)=false := by
    rw [hbefore _ (by dsimp [pos]; omega)]
    simp [original,setAt,clearAt,show h+8≠pos by dsimp [pos]; omega,show h+8≠h+10 by omega]
  have hz9 : out (h+9)=false := by
    rw [hbefore _ (by dsimp [pos]; omega)]
    simp [original,setAt,clearAt,show h+9≠pos by dsimp [pos]; omega,
      show h+9≠h+10 by omega,show h+9≠h+8 by omega,h9]
  have ho10 : out (h+10)=true := by
    rw [hbefore _ (by dsimp [pos]; omega)]
    simp [original,setAt,show h+10≠pos by dsimp [pos]; omega]
  have hc : ∀ q, h+11≤q → q<separator → out q=true := by
    intro q hq hq'
    rw [hbefore q (by dsimp [pos]; omega)]
    simp [original,setAt,clearAt,show q≠pos by dsimp [pos]; omega,
      show q≠h+10 by omega,show q≠h+8 by omega,ones q hq hq']
  have hs : out separator=false := by rw [hframe separator (by omega) (by dsimp [pos]; omega)]; exact sep
  exact ⟨k,out,hk,hr.2.1,hr.1,hbank,hrightframe,hleft,hz8,hz9,ho10,hc,hs,hseg'⟩

theorem positive_operation (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (v : Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ ((v+1)::graphTail))
    (hlong : h+12≤separator) (mark : t (h+8)=true)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    let pos := separator+1+((encode values).length : Int)
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=10 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧
      Holds out (separator+1)
        (encode (arrayBank result.bank) ++ (encode more ++ [true,false,false])) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 23 (pos-2) out) k := by
  obtain ⟨k,out,hk,hs,he,hbank,_,_,_,_,_,_,_,hseg⟩ :=
    positive_operation_full h separator t values graphTail more v bank hlen hgraph hlong mark h9 h10 ones sep word
  exact ⟨k,out,hk,hs,he,hbank,hseg⟩

#print axioms zero_operation_full
#print axioms zero_operation
#print axioms positive_operation_full
#print axioms positive_operation
end Shared.Beeping.NPcoNP.NativeRow10Operation
