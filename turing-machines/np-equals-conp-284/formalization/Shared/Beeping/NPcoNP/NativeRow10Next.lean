import Shared.Beeping.NPcoNP.NativeRow10Return
import Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
import Shared.Beeping.NPcoNP.NativeRow10PositiveCarry
import Shared.Beeping.NPcoNP.NativeSegmentSupport

/-! Both supplied row-10 branches through their literal next selector. -/
namespace Shared.Beeping.NPcoNP.NativeRow10Next
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeRow10Return
open Shared.Beeping.NPcoNP.NativeRow10Operation
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.NativeRow10PositiveCarry
open Shared.Beeping.NPcoNP.NativeSegmentSupport
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- The zero branch implements the row-10 bank test, returns, and reaches
the parsed row-11 path in finite silent time. -/
theorem zero_operation_next_full (h bound separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ (0::graphTail))
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+8)=true) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (right : ∀ q, bound≤q → t q=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode (0::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=11 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧ Holds out (h-4) row11Path ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.6.decnz",14) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+6<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [false,false])) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 93 (h-3) out) k := by
  dsimp only
  obtain ⟨k,mid,hk,hstate,hevent,hbank,hframe,hbefore,h8,h9',h10',hcontrol,hsep,hseg⟩ :=
    zero_operation_return_full h separator t values graphTail more bank hlen hgraph hlong path mark h9 h10 ones sep word
  have hpath : Holds mid (h-4) zeroNextPath := by
    apply holds_transport t mid _ _ path
    intro q hq hq'
    symm
    apply hbefore
    simp [zeroNextPath] at hq'
    omega
  have hleft : ∀ q, q<h-4 → mid q=false := by
    intro q hq
    rw [hbefore q (by omega)]
    exact left q hq
  have hv := hpath
  simp only [zeroNextPath,Holds] at hv
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,p7,_⟩ := hv
  have h7 : mid (h+7)=false := by convert p7 using 1 <;> congr 1 <;> omega
  have hc : ∀ q, h+10≤q → q<separator → mid q=true := by
    intro q hq hq'
    by_cases he : q=h+10
    · simpa only [he] using h10'
    · exact hcontrol q (by omega) hq'
  obtain ⟨endBound,hend⟩ := silent_right_blank machine (cfg 280 (h+9) t)
    (cfg 1 (h+6) mid) k ⟨bound,right⟩ hseg
  obtain ⟨m,out,hm,hnext,hparse,hleft',hgap,hmarker,hsuffix,hcarry⟩ :=
    carry_to_row11_path h endBound separator mid hlong hpath hleft h7 h8 h9' hc hsep hend
  have hout : Holds out (separator+1)
      (encode (arrayBank (target.system.step ⟨10,bank⟩).1.bank) ++ (encode more ++ [false,false])) := by
    apply holds_transport mid out _ _ hbank
    intro q hq _
    exact (hsuffix q (by omega)).symm
  have hf : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hsuffix q hq,hframe q hq]
  have hzero : out separator=false := (hsuffix separator (by omega)).trans hsep
  have all := segAdd machine _ _ _ k m hseg hcarry
  exact ⟨k+m,out,by omega,hstate,hevent,hnext,hparse,hleft',hgap,hmarker,hzero,hout,hf,all⟩


/-- Compatibility interface omitting the control and left frame. -/
theorem zero_operation_next (h bound separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ (0::graphTail))
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+8)=true) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (right : ∀ q, bound≤q → t q=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode (0::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=11 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧ Holds out (h-4) row11Path ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.6.decnz",14) ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [false,false])) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 93 (h-3) out) k := by
  obtain ⟨k,out,hk,hs,he,hpath,hparse,_,_,_,_,hbank,hframe,hseg⟩ :=
    zero_operation_next_full h bound separator t values graphTail more bank hlen hgraph
      hlong path left mark h9 h10 ones sep right word
  exact ⟨k,out,hk,hs,he,hpath,hparse,hbank,hframe,hseg⟩

/-- The positive branch implements the row-10 decrement, returns, and reaches
the distinct `_continue.1` path in finite silent time. -/
theorem positive_operation_next_full (h bound separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (v : Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ ((v+1)::graphTail))
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+8)=true) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (right : ∀ q, bound≤q → t q=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=10 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧ Holds out (h-4) positiveContinuationPath ∧
      parseForward 52 out (h-4)=some ("_continue.1",12) ∧
      (∀ q, positiveFrontier separator values v graphTail more<q → out q=t q) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+7<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [true,false,false])) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 93 (h-3) out) k := by
  dsimp only
  obtain ⟨k,mid,hk,hstate,hevent,hbank,hrightframe,hbefore,h8,h9',h10',hcontrol,hsep,hseg⟩ :=
    positive_operation_return_full h separator t values graphTail more v bank hlen hgraph hlong mark h9 h10 ones sep word
  have hpath : Holds mid (h-4) zeroNextPath := by
    apply holds_transport t mid _ _ path
    intro q hq hq'
    symm
    apply hbefore
    simp [zeroNextPath] at hq'
    omega
  have hleft : ∀ q, q<h-4 → mid q=false := by
    intro q hq
    rw [hbefore q (by omega)]
    exact left q hq
  have hc : ∀ q, h+10≤q → q<separator → mid q=true := by
    intro q hq hq'
    by_cases he : q=h+10
    · simpa only [he] using h10'
    · exact hcontrol q (by omega) hq'
  obtain ⟨endBound,hend⟩ := silent_right_blank machine (cfg 280 (h+9) t)
    (cfg 1 (h+7) mid) k ⟨bound,right⟩ hseg
  obtain ⟨m,out,hm,hnext,hparse,hleft',hgap,hmarker,hsuffix,hcarry⟩ :=
    carry_to_positive_continuation h endBound separator mid hlong hpath hleft h8 h9' hc hsep hend
  have hout : Holds out (separator+1)
      (encode (arrayBank (target.system.step ⟨10,bank⟩).1.bank) ++ (encode more ++ [true,false,false])) := by
    apply holds_transport mid out _ _ hbank
    intro q hq _
    exact (hsuffix q (by omega)).symm
  have hframe : ∀ q, positiveFrontier separator values v graphTail more<q → out q=t q := by
    intro q hq
    have hq' : separator≤q := by
      dsimp [positiveFrontier] at hq
      omega
    exact (hsuffix q hq').trans (hrightframe q hq)
  have hzero : out separator=false := (hsuffix separator (by omega)).trans hsep
  have all := segAdd machine _ _ _ k m hseg hcarry
  exact ⟨k+m,out,by omega,hstate,hevent,hnext,hparse,hframe,hleft',hgap,hmarker,hzero,hout,all⟩

/-- Compatibility interface that forgets the control-gap frame. -/
theorem positive_operation_next (h bound separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (v : Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ ((v+1)::graphTail))
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+8)=true) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (right : ∀ q, bound≤q → t q=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=10 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧ Holds out (h-4) positiveContinuationPath ∧
      parseForward 52 out (h-4)=some ("_continue.1",12) ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [true,false,false])) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 93 (h-3) out) k := by
  obtain ⟨k,out,hk,hstate,hevent,hnext,hparse,_,_,_,_,_,hbank,hseg⟩ :=
    positive_operation_next_full h bound separator t values graphTail more v bank hlen hgraph
      hlong path left mark h9 h10 ones sep right word
  exact ⟨k,out,hk,hstate,hevent,hnext,hparse,hbank,hseg⟩

#print axioms zero_operation_next_full
#print axioms zero_operation_next
#print axioms positive_operation_next_full
#print axioms positive_operation_next
end Shared.Beeping.NPcoNP.NativeRow10Next
