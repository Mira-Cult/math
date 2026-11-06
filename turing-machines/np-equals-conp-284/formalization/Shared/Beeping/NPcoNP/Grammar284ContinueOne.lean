import Shared.Beeping.NPcoNP.Grammar284ContinueOneShape
import Shared.Beeping.NPcoNP.NativeContinueOneGeneric
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! A physical `_continue.1` step reaches the first expanded restart leaf,
under explicit marker and tape-spacing assumptions. Further administrative
leaves and recurrence of these assumptions remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.Grammar284ContinueOne
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeContinueOneGeneric
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284ContinueOneShape
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

theorem continue_one_to_first_restart_exact (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList)
    (name : entry.2="_continue.1") (origin separator : Int) (t : Int → Bool)
    (word : Holds t origin entry.1) (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, origin+((entry.1.length : Nat) : Int)-1<q → q<separator-1 → t q=false)
    (room : origin+55<separator) (right : t (separator-1)=true)
    (sep : t separator=false) :
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      restart traceState557.acc.starts entry.1 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ Holds out origin next ∧ (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧
      out separator=false ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  have listed : entry ∈ traceState557.acc.leaves.toList := by
    have he := expanded
    rw [producerExpand] at he
    cases he
    exact member
  obtain ⟨i,dst,next,nextName,_,hdst,hnext,ilo,ihi,hbit,hsuffix,hshape⟩ :=
    continue_one_shape_sound entry (all_continue_one_shapes entry listed name)
  have nlist : traceState557.acc.leaves.toList[dst]?=some (next,nextName) := by
    simpa only [Array.getElem?_toList] using hnext
  obtain ⟨bound,hget⟩ := List.getElem?_eq_some_iff.mp nlist
  have nmem : (next,nextName) ∈ traceState557.acc.leaves.toList := by
    rw [←hget]
    exact List.getElem_mem bound
  have nwalk : PreparedWalk next (.op nextName) :=
    expanded_leaf_follows traceState557.acc producerExpand (next,nextName) nmem
  have nlen : next.length≤55 := (prepared_path_bound next (.op nextName) nwalk).1
  have elen : entry.1.length≤55 := (expanded_leaf_semantic_bounds e expanded entry member).1
  have ibound : i<entry.1.length := by omega
  have bit : entry.1[i]=true := by
    rw [List.getElem?_eq_getElem ibound] at hbit
    exact Option.some.inj hbit
  have one : t (origin+(i : Int))=true := by rw [holds_get t origin entry.1 word i ibound,bit]
  have inside : ∀ q, origin+(i : Int)<q → q<origin+((entry.1.length : Nat) : Int)-1 → t q=false := by
    intro q hq hq'
    let j := (q-origin).toNat
    have hj : (j : Int)=q-origin := Int.toNat_of_nonneg (by omega)
    have hjlo : i<j := by omega
    have hjhi : j<entry.1.length-1 := by omega
    have hjbound : j<entry.1.length := by omega
    have hz := hsuffix j hjlo hjhi
    rw [List.getElem?_eq_getElem hjbound] at hz
    have hz' : entry.1[j]=false := Option.some.inj hz
    have he : origin+(j : Int)=q := by omega
    simpa only [he,hz'] using holds_get t origin entry.1 word j hjbound
  let zeros := next.length-(entry.1.take i ++ [true]).length
  have hlength : next.length=i+1+zeros := by
    have hh := congrArg List.length hshape
    simpa [zeros, List.length_take_of_le (by omega : i ≤ entry.1.length),
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  have hroom : origin+(i : Int)+(zeros : Int)<separator-1 := by omega
  have hspace : origin+((entry.1.length : Nat) : Int)+1≤separator := by omega
  obtain ⟨steps,out,hsteps,hout,hleftout,hgap,hright,hsep,hbank,hsegment⟩ :=
    continue_one_to_candidate_exact e expanded entry member name origin separator t i zeros ilo ihi
      word left one inside gap hroom hspace right sep
  have hh : next=entry.1.take i ++ true::List.replicate zeros false := by
    simpa only [zeros,List.append_assoc,List.singleton_append] using hshape
  have hgapNext : ∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false := by
    intro q hq hq'
    apply hgap q _ hq'
    rw [←hh]
    omega
  refine ⟨dst,next,nextName,steps,out,hdst,hnext,hsteps,?_,hleftout,hgapNext,hright,hsep,hbank,hsegment⟩
  simpa only [hh] using hout

/-- Original interface with the word and bank conclusions. -/
theorem continue_one_to_first_restart (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList)
    (name : entry.2="_continue.1") (origin separator : Int) (t : Int → Bool)
    (word : Holds t origin entry.1) (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, origin+((entry.1.length : Nat) : Int)-1<q → q<separator-1 → t q=false)
    (room : origin+55<separator) (right : t (separator-1)=true)
    (sep : t separator=false) :
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      restart traceState557.acc.starts entry.1 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ Holds out origin next ∧ out (separator-1)=true ∧
      out separator=false ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hdst,hnext,hs,hw,_,_,hr,hsep,hbank,hseg⟩ := continue_one_to_first_restart_exact e expanded entry member name origin separator t word left gap room right sep
  exact ⟨dst,next,nextName,steps,out,hdst,hnext,hs,hw,hr,hsep,hbank,hseg⟩

#print axioms continue_one_to_first_restart_exact
#print axioms continue_one_to_first_restart
end Shared.Beeping.NPcoNP.Grammar284ContinueOne
