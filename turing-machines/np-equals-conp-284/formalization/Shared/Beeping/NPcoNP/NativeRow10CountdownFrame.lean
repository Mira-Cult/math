import Shared.Beeping.NPcoNP.NativeRow10CountdownFull
import Shared.Beeping.NPcoNP.NativeSegmentSupport

/-! The complete row-10 countdown with its final tape frame. -/
namespace Shared.Beeping.NPcoNP.NativeRow10CountdownFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeRow10Next
open Shared.Beeping.NPcoNP.NativeRow10Padded
open Shared.Beeping.NPcoNP.NativeRow10Array
open Shared.Beeping.NPcoNP.NativeRow10Operation
open Shared.Beeping.NPcoNP.NativeRow10CountdownFull
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.NativeSegmentSupport
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

theorem countdown_to_row11_exact_tail (n : Nat) (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12)
    (ready : Ready h separator t values graphTail more n bank) :
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧
      (target.system.advance ⟨10,bank⟩ (n+1)).state=11 ∧
      target.system.wordFrom ⟨10,bank⟩ (n+1)=[] ∧
      arrayBank (target.system.advance ⟨10,bank⟩ (n+1)).bank=values ++ (0::graphTail) ∧
      Holds out (h-4) row11Path ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.6.decnz",14) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+6<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1)
        (encode (arrayBank (target.system.advance ⟨10,bank⟩ (n+1)).bank) ++
          (encode (more++List.replicate n 0) ++ [false,false])) ∧
      (∀ q, bankEnd separator values 0 graphTail (more++List.replicate n 0)≤q → out q=false) ∧
      (∃ b : Int, ∀ q, b≤q → out q=false) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 93 (h-3) out) k := by
  induction n generalizing t more bank with
  | zero =>
    obtain ⟨k,out,hk,hs,he,hpath,hparse,hleft,hgap,hmark,hsep,hbank,hsuffix,hseg⟩ :=
      zero_operation_next_full h (bankEnd separator values 0 graphTail more) separator t
        values graphTail more bank ready.length ready.graph ready.long ready.path ready.left
        ready.mark ready.h9 ready.h10 ready.control ready.sep ready.tail ready.word
    obtain ⟨b,hblank⟩ := silent_right_blank machine (cfg 280 (h+9) t)
      (cfg 93 (h-3) out) k ⟨bankEnd separator values 0 graphTail more,ready.tail⟩ hseg
    have htail : ∀ q, bankEnd separator values 0 graphTail (more++List.replicate 0 0)≤q → out q=false := by
      intro q hq
      have hq' : bankEnd separator values 0 graphTail more≤q := by simpa using hq
      have hs : separator≤q := by dsimp [bankEnd] at hq'; omega
      exact (hsuffix q hs).trans (ready.tail q hq')
    have hg := row10_array bank values 0 graphTail ready.length ready.graph
    simp only [if_pos rfl] at hg
    refine ⟨k,out,hk,?_,?_,?_,hpath,hparse,hleft,hgap,hmark,hsep,?_,htail,⟨b,hblank⟩,hseg⟩
    · simpa [WordEventSystem.advance] using hs
    · simpa [WordEventSystem.wordFrom,WordEventSystem.advance] using he
    · simpa [WordEventSystem.advance] using hg.2.2
    · simpa [WordEventSystem.advance] using hbank
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
    obtain ⟨k,out,hk,hs,he,hgraphfinal,hnext,hparse,hleft',hgap,hmark,hsep',hbank',htailfinal,hblank,hrest⟩ := ih mid (more++[0]) next rnext
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
    have hbank'' : Holds out (separator+1)
        (encode (arrayBank (target.system.advance ⟨10,bank⟩ ((n+1)+1)).bank) ++
          (encode (more++List.replicate (n+1) 0) ++ [false,false])) := by
      rw [advance]
      simpa [List.replicate_succ,List.append_assoc] using hbank'
    refine ⟨m+k,out,by omega,?_,?_,?_,hnext,hparse,hleft',hgap,hmark,hsep',hbank'',?_,hblank,
      segAdd machine _ _ _ m k hseg hrest⟩
    · simpa [advance] using hs
    · simpa [word] using he
    · simpa [advance] using hgraphfinal
    · simpa [List.replicate_succ,List.append_assoc] using htailfinal

/-- Compatibility projection of the countdown frame. -/
theorem countdown_to_row11_framed (n : Nat) (h separator : Int) (t : Int → Bool)
    (values graphTail more : List Nat) (bank : Bank 12)
    (ready : Ready h separator t values graphTail more n bank) :
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧
      (target.system.advance ⟨10,bank⟩ (n+1)).state=11 ∧
      target.system.wordFrom ⟨10,bank⟩ (n+1)=[] ∧
      arrayBank (target.system.advance ⟨10,bank⟩ (n+1)).bank=values ++ (0::graphTail) ∧
      Holds out (h-4) row11Path ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.6.decnz",14) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+6<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1)
        (encode (arrayBank (target.system.advance ⟨10,bank⟩ (n+1)).bank) ++
          (encode (more++List.replicate n 0) ++ [false,false])) ∧
      (∃ b : Int, ∀ q, b≤q → out q=false) ∧
      silentSegment machine (cfg 280 (h+9) t) (cfg 93 (h-3) out) k := by
  obtain ⟨k,out,hk,hs,he,hgraph,hpath,hparse,hleft,hgap,hmark,hsep,hbank,_,hblank,hseg⟩ :=
    countdown_to_row11_exact_tail n h separator t values graphTail more bank ready
  exact ⟨k,out,hk,hs,he,hgraph,hpath,hparse,hleft,hgap,hmark,hsep,hbank,hblank,hseg⟩

#print axioms countdown_to_row11_exact_tail
#print axioms countdown_to_row11_framed
end Shared.Beeping.NPcoNP.NativeRow10CountdownFrame
