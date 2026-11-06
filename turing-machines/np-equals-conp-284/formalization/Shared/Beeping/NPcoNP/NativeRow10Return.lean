import Shared.Beeping.NPcoNP.NativeRow10Operation
import Shared.Beeping.NPcoNP.NativeBankReturnGeneric
import Shared.Beeping.NPcoNP.NativeBankReturn23Generic
import Shared.Beeping.NPcoNP.NativeFifthZeroNextPath

/-! Both physical row-10 operation branches return to state 1. -/
namespace Shared.Beeping.NPcoNP.NativeRow10Return
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeBankReturnGeneric
open Shared.Beeping.NPcoNP.NativeBankReturn23Generic
open Shared.Beeping.NPcoNP.NativeRow10Operation
open Shared.Beeping.NPcoNP.NativeRow10Array
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- A zero row-10 operation returns to state 1, preserving the graph bank
and the whole bank suffix. The following carry remains separate. -/
theorem zero_operation_return_full (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ (0::graphTail))
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (mark : t (h+8)=true) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode (0::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=11 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [false,false])) ∧
      (∀ q, separator≤q → out q=t q) ∧
      (∀ q, q<h+8 → out q=t q) ∧ out (h+8)=false ∧ out (h+9)=false ∧
      out (h+10)=true ∧ (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 1 (h+6) out) k := by
  dsimp only
  obtain ⟨k,out,hk,hstate,hevent,hbank,hframe,hbefore,h8,h9',h10',hcontrol,hsep,hseg⟩ :=
    zero_operation_full h separator t values graphTail more bank hlen hgraph hlong mark h9 h10 ones sep word
  have hv := path
  simp only [zeroNextPath,Holds] at hv
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,p7,_⟩ := hv
  have ht7 : t (h+7)=false := by convert p7 using 1 <;> congr 1 <;> omega
  have hp1 : out ((h+6)+1)=false := by
    have he : h+6+1=h+7 := by omega
    rw [he,hbefore _ (by omega)]
    exact ht7
  have hp2 : out ((h+6)+2)=false := by simpa only [show h+6+2=h+8 by omega] using h8
  have hp3 : out ((h+6)+3)=false := by simpa only [show h+6+3=h+9 by omega] using h9'
  have hc : ∀ q, (h+6)+4≤q → q<separator → out q=true := by
    intro q hq hq'
    by_cases he : q=h+10
    · simpa only [he] using h10'
    · exact hcontrol q (by omega) hq'
  have hpref : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) (encode values) _ word
  have hpref' : Holds out (separator+1) (encode values ++ []) := by
    have ho : Holds out (separator+1) (encode values) := by
      apply NativeHalfScannerFrames.holds_transport t out _ _ hpref
      intro q hq _
      exact (hframe q (by omega)).symm
    simpa using ho
  have hreturn := return25_generic_min_gap (h+6) separator out values [] (by omega)
    hp1 hp2 hp3 hc hsep hpref'
  let duration := (unaryBankPrefix (separator-((h+6)+6)).toNat values).length+5
  let pos := separator+1+((encode values).length : Int)
  have hreturn' : silentSegment machine (cfg 25 (pos-1) out) (cfg 1 (h+6) out) duration := by
    have he : separator+((encode values).length : Int)=pos-1 := by dsimp [pos]; omega
    simpa only [he,duration] using hreturn
  have all := segAdd machine _ _ _ k duration hseg hreturn'
  exact ⟨k+duration,out,by dsimp [duration]; omega,hstate,hevent,hbank,hframe,hbefore,h8,h9',h10',hcontrol,hsep,all⟩

theorem zero_operation_return (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ (0::graphTail))
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (mark : t (h+8)=true) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode (0::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=11 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [false,false])) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 1 (h+6) out) k := by
  obtain ⟨k,out,hk,hs,he,hbank,hframe,_,_,_,_,_,_,hseg⟩ :=
    zero_operation_return_full h separator t values graphTail more bank hlen hgraph hlong path mark h9 h10 ones sep word
  exact ⟨k,out,hk,hs,he,hbank,hframe,hseg⟩

/-- A positive row-10 operation returns to state 1 with its decremented
bank. The compiler continuation following the return remains separate. -/
theorem positive_operation_return_full (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (v : Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ ((v+1)::graphTail))
    (hlong : h+12≤separator) (mark : t (h+8)=true)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=10 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [true,false,false])) ∧
      (∀ q, positiveFrontier separator values v graphTail more<q → out q=t q) ∧
      (∀ q, q<h+8 → out q=t q) ∧ out (h+8)=false ∧ out (h+9)=false ∧
      out (h+10)=true ∧ (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 1 (h+7) out) k := by
  dsimp only
  obtain ⟨k,out,hk,hstate,hevent,hbank,hrightframe,hbefore,h8,h9',h10',hcontrol,hsep,hseg⟩ :=
    positive_operation_full h separator t values graphTail more v bank hlen hgraph hlong mark h9 h10 ones sep word
  have hr := row10_array bank values (v+1) graphTail hlen hgraph
  have hnonzero : v+1≠0 := by omega
  simp only [hnonzero,if_false,Nat.add_sub_cancel_right] at hr
  have hbank' : Holds out (separator+1)
      (encode values ++ (encode (v::graphTail) ++ (encode more ++ [true,false,false]))) := by
    have hw := hbank
    rw [hr.2.2] at hw
    simpa [encode_append,encode,List.append_assoc] using hw
  have hp1 : out ((h+7)+1)=false := by simpa only [show h+7+1=h+8 by omega] using h8
  have hp2 : out ((h+7)+2)=false := by simpa only [show h+7+2=h+9 by omega] using h9'
  have hm : out ((h+7)+3)=true := by simpa only [show h+7+3=h+10 by omega] using h10'
  have hc : ∀ q, (h+7)+4≤q → q<separator → out q=true := by
    intro q hq hq'
    exact hcontrol q (by omega) hq'
  have hreturn := return23_generic_weak (h+7) separator out values
    (encode (v::graphTail) ++ (encode more ++ [true,false,false]))
    (by omega) hp1 hp2 hm hc hsep hbank'
  let duration := (unaryBankPrefix (separator-((h+7)+5)).toNat values).length+3
  let pos := separator+1+((encode values).length : Int)
  have hreturn' : silentSegment machine (cfg 23 (pos-2) out) (cfg 1 (h+7) out) duration := by
    have he : separator+((encode values).length : Int)-1=pos-2 := by dsimp [pos]; omega
    simpa only [he,duration] using hreturn
  have all := segAdd machine _ _ _ k duration hseg hreturn'
  exact ⟨k+duration,out,by dsimp [duration]; omega,hstate,hevent,hbank,hrightframe,hbefore,h8,h9',h10',hcontrol,hsep,all⟩

theorem positive_operation_return (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (v : Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ ((v+1)::graphTail))
    (hlong : h+12≤separator) (mark : t (h+8)=true)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=10 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [true,false,false])) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 1 (h+7) out) k := by
  obtain ⟨k,out,hk,hs,he,hbank,_,_,_,_,_,_,_,hseg⟩ :=
    positive_operation_return_full h separator t values graphTail more v bank hlen hgraph hlong mark h9 h10 ones sep word
  exact ⟨k,out,hk,hs,he,hbank,hseg⟩

#print axioms zero_operation_return_full
#print axioms zero_operation_return
#print axioms positive_operation_return_full
#print axioms positive_operation_return
end Shared.Beeping.NPcoNP.NativeRow10Return
