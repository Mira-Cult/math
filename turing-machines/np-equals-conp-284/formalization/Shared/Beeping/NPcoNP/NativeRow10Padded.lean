import Shared.Beeping.NPcoNP.NativeRow10PositiveLoopStep

/-! A blank-tail invariant for repeated positive row-10 scanner entries. -/
namespace Shared.Beeping.NPcoNP.NativeRow10Padded
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeManyBankResult
open Shared.Beeping.NPcoNP.NativeManyShift
open Shared.Beeping.NPcoNP.NativeManySelectorReturn
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeRow10Operation
open Shared.Beeping.NPcoNP.NativeRow10PositiveLoopStep
open Shared.Beeping.NPcoNP.NativeRow10Array
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- A decrement and appended zero reserve move the next positive frontier
one cell right. -/
theorem frontier_next (separator : Int) (values : List Nat) (v : Nat)
    (graphTail more : List Nat) :
    positiveFrontier separator values (v+1) graphTail more + 1 =
      positiveFrontier separator values v graphTail (more++[0]) := by
  simp only [positiveFrontier, List.append_assoc, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.replicate_one, List.append_nil,
    List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  push_cast
  omega

/-- If every cell past the changed interval was blank, re-entry retains a
blank tail and supplies the two padding cells for the next row-10 scan. -/
theorem positive_reenter_padded (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (v : Nat) (bank : Bank 12) (hlen : values.length=6)
    (hgraph : arrayBank bank=values ++ ((v+1)::graphTail))
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+8)=true) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (tail : ∀ q, positiveFrontier separator values v graphTail more<q → t q=false)
    (word : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false]))) :
    let result := (target.system.step ⟨10,bank⟩).1
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧ result.state=10 ∧
      (target.system.step ⟨10,bank⟩).2=[] ∧ Holds out (h-4) zeroNextPath ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+8)=true ∧
      out (h+9)=false ∧ out (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      Holds out (separator+1)
        (encode (values ++ (v::graphTail)) ++ (encode (more++[0]) ++ [false,false])) ∧
      (∀ q, positiveFrontier separator values v graphTail more<q → out q=false) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 280 (h+9) out) k := by
  dsimp only
  let f := positiveFrontier separator values v graphTail more
  have right : ∀ q, f+1≤q → t q=false := by
    intro q hq
    exact tail q (by omega)
  obtain ⟨k,out,hk,hs,he,hpath,hframe,hleft,h8,h9',h10',hc,hsep,hbank,hseg⟩ :=
    positive_operation_reenter h (f+1) separator t values graphTail more v bank hlen hgraph
      hlong path left mark h9 h10 ones sep right word
  have hright : ∀ q, f<q → out q=false := by
    intro q hq
    rw [hframe q hq]
    exact tail q hq
  have hr := row10_array bank values (v+1) graphTail hlen hgraph
  simp only [show v+1≠0 by omega,if_false,Nat.add_sub_cancel_right] at hr
  rw [hr.2.2] at hbank
  let suffix := List.replicate v true ++ (graphTail++more).flatMap (fun z => false :: List.replicate (z+1) true)
  have hlen' : (encode (v::(graphTail++more))).length=suffix.length+2 := by
    have hx := prefix_length v (graphTail++more)
    simp only [unaryBankPrefix,List.length_append,List.length_replicate,List.length_flatMap] at hx
    dsimp [suffix]
    simp only [List.length_append,List.length_replicate,List.length_flatMap]
    omega
  let ws := encode values ++ (encode (v::(graphTail++more)) ++ [true,false,false])
  have hw : Holds out (separator+1) ws := by
    simpa [ws,encode_append,encode,List.append_assoc] using hbank
  have hend : separator+1+(ws.length : Int)=f+3 := by
    dsimp [ws,f,positiveFrontier]
    simp only [List.length_append,List.length_cons,List.length_nil]
    rw [hlen']
    dsimp [suffix]
    simp only [List.length_append,List.length_replicate]
    push_cast
    omega
  have hlast : Holds out (separator+1+(ws.length : Int)) [false] := by
    rw [hend]
    exact ⟨hright _ (by omega),trivial⟩
  have hpadded := holds_append_intro out (separator+1) ws [false] hw hlast
  have hpadded' : Holds out (separator+1)
      (encode (values ++ (v::graphTail)) ++ (encode (more++[0]) ++ [false,false])) := by
    simpa [ws,encode_append,encode,List.append_assoc] using hpadded
  exact ⟨k,out,hk,hs,he,hpath,hleft,h8,h9',h10',hc,hsep,hpadded',hright,hseg⟩

#print axioms frontier_next
#print axioms positive_reenter_padded
end Shared.Beeping.NPcoNP.NativeRow10Padded
