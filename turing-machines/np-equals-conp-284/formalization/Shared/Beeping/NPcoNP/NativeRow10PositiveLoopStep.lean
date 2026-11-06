import Shared.Beeping.NPcoNP.NativeRow10Next
import Shared.Beeping.NPcoNP.NativeRow10Continuation

/-! One complete positive row-10 physical operation and scanner re-entry. -/
namespace Shared.Beeping.NPcoNP.NativeRow10PositiveLoopStep
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeRow10Next
open Shared.Beeping.NPcoNP.NativeRow10Operation
open Shared.Beeping.NPcoNP.NativeRow10Continuation
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- On a supplied prepared layout, a positive graph row-10 test decrements the
selected register and physically re-enters its scanner in finite silent time.
The extra encoded zero block is retained explicitly in the resulting bank word. -/
theorem positive_operation_reenter (h bound separator : Int) (t : Int → Bool)
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
      (target.system.step ⟨10,bank⟩).2=[] ∧ Holds out (h-4) zeroNextPath ∧
      (∀ q, positiveFrontier separator values v graphTail more<q → out q=t q) ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+8)=true ∧
      out (h+9)=false ∧ out (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.bank) ++ (encode more ++ [true,false,false])) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 280 (h+9) out) k := by
  dsimp only
  obtain ⟨k,mid,hk,hs,he,hp,_,hrightframe,hl,hg,hm,hzero,hbank,hseg⟩ :=
    positive_operation_next_full h bound separator t values graphTail more v bank hlen hgraph
      hlong path left mark h9 h10 ones sep right word
  obtain ⟨m,hm',hpath,hleft,h8,h9',h10',hcontrol,hframe,hprep⟩ :=
    continuation_and_prepare h separator mid hlong hp hl hg hm
  let out := fillRange (setAt (h+8) (put mid (h+7) false)) (h+11) (separator-1)
  have hright : ∀ q, positiveFrontier separator values v graphTail more<q → out q=t q := by
    intro q hq
    have hq' : separator≤q := by dsimp [positiveFrontier] at hq; omega
    exact (hframe q hq').trans (hrightframe q hq)
  have hsep : out separator=false := (hframe separator (by omega)).trans hzero
  have hout : Holds out (separator+1)
      (encode (arrayBank (target.system.step ⟨10,bank⟩).1.bank) ++ (encode more ++ [true,false,false])) := by
    apply holds_transport mid out _ _ hbank
    intro q hq _
    exact (hframe q (by omega)).symm
  exact ⟨k+m,out,by omega,hs,he,hpath,hright,hleft,h8,h9',h10',hcontrol,hsep,hout,
    segAdd machine _ _ _ k m hseg hprep⟩

#print axioms positive_operation_reenter
end Shared.Beeping.NPcoNP.NativeRow10PositiveLoopStep
