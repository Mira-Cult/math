import Shared.Beeping.NPcoNP.NativeRow10Padded
import Shared.Beeping.NPcoNP.NativeRow10ZeroCarry

/-! Finite positive row-10 repetitions and zero exit on a supplied tape. -/
namespace Shared.Beeping.NPcoNP.NativeRow10CountdownFull
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeRow10Operation
open Shared.Beeping.NPcoNP.NativeRow10Next
open Shared.Beeping.NPcoNP.NativeRow10Padded
open Shared.Beeping.NPcoNP.NativeRow10Array
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

def bankEnd (separator : Int) (values : List Nat) (n : Nat)
    (graphTail more : List Nat) : Int :=
  separator+1+((encode values ++ encode (n::(graphTail++more))).length : Int)

theorem positive_frontier_end (separator : Int) (values : List Nat) (v : Nat)
    (graphTail more : List Nat) :
    positiveFrontier separator values v graphTail more + 1 =
      bankEnd separator values (v+1) graphTail more := by
  have hlen : (encode ((v+1)::(graphTail++more))).length =
      (List.replicate v true ++ (graphTail++more).flatMap
        (fun z => false :: List.replicate (z+1) true)).length+3 := by
    have hx := prefix_length (v+1) (graphTail++more)
    simp only [unaryBankPrefix,List.length_append,List.length_replicate,List.length_flatMap] at hx
    simp only [List.length_append,List.length_replicate,List.length_flatMap]
    omega
  dsimp [positiveFrontier,bankEnd]
  simp only [List.length_append]
  rw [hlen]
  simp only [List.length_append,List.length_replicate]
  push_cast
  omega

theorem bank_end_next (separator : Int) (values : List Nat) (n : Nat)
    (graphTail more : List Nat) :
    bankEnd separator values n graphTail (more++[0]) =
      bankEnd separator values (n+1) graphTail more+1 := by
  dsimp [bankEnd]
  simp only [encode_append,encode,block,List.length_append,List.length_cons,
    List.length_replicate,List.length_nil]
  push_cast
  omega

structure Ready (h separator : Int) (t : Int → Bool) (values graphTail more : List Nat)
    (n : Nat) (bank : Bank 12) : Prop where
  length : values.length=6
  graph : arrayBank bank=values ++ (n::graphTail)
  long : h+12≤separator
  path : Holds t (h-4) zeroNextPath
  left : ∀ q, q<h-4 → t q=false
  mark : t (h+8)=true
  h9 : t (h+9)=false
  h10 : t (h+10)=false
  control : ∀ q, h+11≤q → q<separator → t q=true
  sep : t separator=false
  tail : ∀ q, bankEnd separator values n graphTail more≤q → t q=false
  word : Holds t (separator+1)
    (encode values ++ (encode (n::(graphTail++more)) ++ [false,false]))

/-- A supplied bank value executes all positive decrements and the final zero
branch in finite silent time. The graph takes exactly n+1 steps to row 11. -/
theorem countdown_to_row11 (n : Nat) (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12)
    (ready : Ready h separator t values graphTail more n bank) :
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧
      (target.system.advance ⟨10,bank⟩ (n+1)).state=11 ∧
      target.system.wordFrom ⟨10,bank⟩ (n+1)=[] ∧
      Holds out (h-4) row11Path ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.6.decnz",14) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 93 (h-3) out) k := by
  induction n generalizing t more bank with
  | zero =>
    obtain ⟨k,out,hk,hs,he,hpath,hparse,_,_,hseg⟩ :=
      zero_operation_next h (bankEnd separator values 0 graphTail more) separator t
        values graphTail more bank ready.length ready.graph ready.long ready.path ready.left
        ready.mark ready.h9 ready.h10 ready.control ready.sep ready.tail ready.word
    refine ⟨k,out,hk,?_,?_,hpath,hparse,hseg⟩
    · simpa [WordEventSystem.advance] using hs
    · simpa [WordEventSystem.wordFrom,WordEventSystem.advance] using he
  | succ n ih =>
    have hgraph : arrayBank bank=values ++ ((n+1)::graphTail) := by simpa using ready.graph
    have hword : Holds t (separator+1)
        (encode values ++ (encode ((n+1)::(graphTail++more)) ++ [false,false])) := by simpa using ready.word
    have htail : ∀ q, positiveFrontier separator values n graphTail more<q → t q=false := by
      intro q hq
      apply ready.tail
      rw [← positive_frontier_end separator values n graphTail more]
      omega
    obtain ⟨m,mid,hm,hstate,hevent,hpath,hleft,h8,h9,h10,hcontrol,hsep,hbank,htail',hseg⟩ :=
      positive_reenter_padded h separator t values graphTail more n bank ready.length hgraph
        ready.long ready.path ready.left ready.mark ready.h9 ready.h10 ready.control ready.sep htail hword
    let next := (target.system.step ⟨10,bank⟩).1.bank
    have hcfg : (target.system.step ⟨10,bank⟩).1=⟨10,next⟩ := by
      cases hc : (target.system.step ⟨10,bank⟩).1 with
      | mk st bk => simp_all [next]
    have hr := row10_array bank values (n+1) graphTail ready.length hgraph
    simp only [show n+1≠0 by omega,if_false,Nat.add_sub_cancel_right] at hr
    have hgraph' : arrayBank next=values ++ (n::graphTail) := hr.2.2
    have htail'' : ∀ q, bankEnd separator values n graphTail (more++[0])≤q → mid q=false := by
      intro q hq
      apply htail'
      rw [bank_end_next,← positive_frontier_end] at hq
      omega
    have hword' : Holds mid (separator+1)
        (encode values ++ (encode (n::(graphTail++(more++[0]))) ++ [false,false])) := by
      simpa [encode_append,encode,List.append_assoc] using hbank
    have rnext : Ready h separator mid values graphTail (more++[0]) n next :=
      ⟨ready.length,hgraph',ready.long,hpath,hleft,h8,h9,h10,hcontrol,hsep,htail'',hword'⟩
    obtain ⟨k,out,hk,hs,he,hnext,hparse,hrest⟩ := ih mid (more++[0]) next rnext
    have advance : target.system.advance ⟨10,bank⟩ ((n+1)+1) =
        target.system.advance ⟨10,next⟩ (n+1) := by
      have heq : (n+1)+1=1+(n+1) := by omega
      rw [heq,WordEventSystem.advance_add]
      simpa [WordEventSystem.advance,hcfg]
    have word : target.system.wordFrom ⟨10,bank⟩ ((n+1)+1) =
        target.system.wordFrom ⟨10,next⟩ (n+1) := by
      have heq : (n+1)+1=1+(n+1) := by omega
      rw [heq,WordEventSystem.wordFrom_add]
      simpa [WordEventSystem.wordFrom,WordEventSystem.advance,hcfg,hevent]
    refine ⟨m+k,out,by omega,?_,?_,hnext,hparse,segAdd machine _ _ _ m k hseg hrest⟩
    · simpa [advance] using hs
    · simpa [word] using he

#print axioms positive_frontier_end
#print axioms bank_end_next
#print axioms countdown_to_row11
end Shared.Beeping.NPcoNP.NativeRow10CountdownFull
