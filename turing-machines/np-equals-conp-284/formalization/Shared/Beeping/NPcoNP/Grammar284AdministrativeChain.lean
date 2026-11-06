import Shared.Beeping.NPcoNP.Grammar284ContinueOne
import Shared.Beeping.NPcoNP.Grammar284ContinueTwo
import Shared.Beeping.NPcoNP.Grammar284BreakOne
import Shared.Beeping.NPcoNP.Grammar284BreakTwo

/-! Finite chains of all four administrative jumps preserve the control
window and bank. Deriving graph chains and reachable layouts remains separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284AdministrativeChain
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284ContinueOne
open Shared.Beeping.NPcoNP.Grammar284ContinueTwo
open Shared.Beeping.NPcoNP.Grammar284BreakOne
open Shared.Beeping.NPcoNP.Grammar284BreakTwo
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

/-- One of the four grammar administrative jumps to its expanded destination. -/
def AdministrativeJump (entry : Path × String) (dst : Nat) : Prop :=
  (entry.2="_continue.1" ∧ restart traceState557.acc.starts entry.1 1=some dst) ∨
  (entry.2="_continue.2" ∧ restart traceState557.acc.starts entry.1 2=some dst) ∨
  (entry.2="_break.1" ∧ successor traceState557.acc.starts entry.1 1=some dst) ∨
  (entry.2="_break.2" ∧ successor traceState557.acc.starts entry.1 2=some dst)

/-- A supplied finite sequence of actual expanded administrative jumps. -/
inductive AdministrativeChain : Nat → (Path × String) → (Path × String) → Prop
  | nil (entry) : AdministrativeChain 0 entry entry
  | cons (n : Nat) (entry middle final : Path × String) (dst : Nat)
      (jump : AdministrativeJump entry dst)
      (leafAt : traceState557.acc.leaves[dst]?=some middle)
      (tail : AdministrativeChain n middle final) : AdministrativeChain (n+1) entry final

/-- Every supplied finite administrative chain executes silently, preserving
its parser window, left blank region and bank. Each jump takes positive time. -/
theorem chain_runs (count : Nat) (entry final : Path × String)
    (chain : AdministrativeChain count entry final) (origin separator : Int) (t : Int → Bool)
    (member : entry ∈ traceState557.acc.leaves.toList)
    (word : Holds t origin entry.1) (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, origin+((entry.1.length : Nat) : Int)-1<q → q<separator-1 → t q=false)
    (room : origin+55<separator) (right : t (separator-1)=true) (sep : t separator=false) :
    ∃ steps out, count≤steps ∧ final ∈ traceState557.acc.leaves.toList ∧
      Holds out origin final.1 ∧ (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((final.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  induction chain generalizing t with
  | nil entry =>
    refine ⟨0,t,by omega,member,word,left,gap,right,sep,by intro q hq; rfl,?_⟩
    simp [silentSegment, WordEventSystem.advance, WordEventSystem.wordFrom]
  | cons n entry middle final dst jump leafAt tail ih =>
    have first : ∃ steps out, 0<steps ∧ Holds out origin middle.1 ∧
        (∀ q, q<origin → out q=false) ∧
        (∀ q, origin+((middle.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
        out (separator-1)=true ∧ out separator=false ∧
        (∀ q, separator≤q → out q=t q) ∧
        silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
      rcases jump with ⟨hname,hdst⟩ | ⟨hname,hdst⟩ | ⟨hname,hdst⟩ | ⟨hname,hdst⟩
      · obtain ⟨d,next,nextName,steps,out,hd,hl,hs,hw,hleft,hgap,hr,hsep,hbank,hseg⟩ :=
          continue_one_to_first_restart_exact traceState557.acc producerExpand entry member hname
            origin separator t word left gap room right sep
        have dEq : d=dst := Option.some.inj (hd.symm.trans hdst)
        subst d
        have mEq : (next,nextName)=middle := Option.some.inj (hl.symm.trans leafAt)
        cases mEq
        exact ⟨steps,out,hs,hw,hleft,hgap,hr,hsep,hbank,hseg⟩
      · obtain ⟨d,next,nextName,steps,out,hd,hl,hs,hw,hleft,hgap,hr,hsep,hbank,hseg⟩ :=
          continue_two_to_first_restart_exact traceState557.acc producerExpand entry member hname
            origin separator t word left gap room right sep
        have dEq : d=dst := Option.some.inj (hd.symm.trans hdst)
        subst d
        have mEq : (next,nextName)=middle := Option.some.inj (hl.symm.trans leafAt)
        cases mEq
        exact ⟨steps,out,hs,hw,hleft,hgap,hr,hsep,hbank,hseg⟩
      · obtain ⟨d,next,nextName,steps,out,hd,hl,hs,hw,hleft,hgap,hr,hsep,hbank,hseg⟩ :=
          break_one_to_first_successor entry member hname
            origin separator t word left gap room right sep
        have dEq : d=dst := Option.some.inj (hd.symm.trans hdst)
        subst d
        have mEq : (next,nextName)=middle := Option.some.inj (hl.symm.trans leafAt)
        cases mEq
        exact ⟨steps,out,hs,hw,hleft,hgap,hr,hsep,hbank,hseg⟩
      · obtain ⟨d,next,nextName,steps,out,hd,hl,hs,hw,hleft,hgap,hr,hsep,hbank,hseg⟩ :=
          break_two_to_first_successor entry member hname
            origin separator t word left gap room right sep
        have dEq : d=dst := Option.some.inj (hd.symm.trans hdst)
        subst d
        have mEq : (next,nextName)=middle := Option.some.inj (hl.symm.trans leafAt)
        cases mEq
        exact ⟨steps,out,hs,hw,hleft,hgap,hr,hsep,hbank,hseg⟩
    have middleList : traceState557.acc.leaves.toList[dst]?=some middle := by
      simpa only [Array.getElem?_toList] using leafAt
    obtain ⟨bound,hget⟩ := List.getElem?_eq_some_iff.mp middleList
    have middleMember : middle ∈ traceState557.acc.leaves.toList := by
      rw [←hget]
      exact List.getElem_mem bound
    obtain ⟨a,u,ha,hu,hul,hug,hur,hus,hubank,hfirst⟩ := first
    obtain ⟨b,v,hb,hmem,hv,hvl,hvg,hvr,hvs,hvbank,hrest⟩ :=
      ih u middleMember hu hul hug hur hus
    refine ⟨a+b,v,by omega,hmem,hv,hvl,hvg,hvr,hvs,?_,segAdd machine _ _ _ a b hfirst hrest⟩
    intro q hq
    exact (hvbank q hq).trans (hubank q hq)

#print axioms chain_runs
end Shared.Beeping.NPcoNP.Grammar284AdministrativeChain
