import Shared.Beeping.NPcoNP.Grammar284SuccessorShape
import Shared.Beeping.NPcoNP.NativeCarryPivot

/-! A literal carry produces the first expanded grammar successor leaf for
ordinary non-root graph rows. Administrative jump execution, operation-to-carry
composition and recurrence of the window remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeCarryPivot
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- For an ordinary non-root graph row, a compatible carry window produces
exactly the first full-grammar successor leaf at the same parser origin.
For decrement, skip 0 is the positive branch and skip 1 the zero branch.
The result can be an administrative leaf, whose execution is not included. -/
theorem carry_to_first_successor_exact (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (increment : Bool) (operation : namedOperation name=some (n,increment))
    (skip : Nat) (hskip : skip=0 ∨ skip=1) (branch : skip=1 → increment=false)
    (t : Int → Bool) (origin h p separator : Int)
    (hpos : h=origin+((path.length-skip : Nat) : Int)-1)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (hp : h<p) (hone : t p=true)
    (between : ∀ q, h<q → q<p → t q=false) (hsep : p+1<separator)
    (ones : ∀ q, p<q → q<separator → t q=true) (blank : t separator=false) :
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path skip=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      PreparedWalk next (.op nextName) ∧ 0<steps ∧ Holds out origin next ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  have shapeChecks := ordinary_successor_shapes state path name leaf notRoot n increment operation
  have selected : successorShape path skip=true ∧ rightmostOK path skip=true := by
    rcases hskip with h0 | h1
    · subst skip
      exact ⟨shapeChecks.1,shapeChecks.2.1⟩
    · subst skip
      have hdec := shapeChecks.2.2 (branch rfl)
      exact ⟨hdec.1,hdec.2.1⟩
  obtain ⟨i,dst,next,nextName,hi,hsucc,hnext,hshape⟩ := successor_shape_sound path skip selected.1
  obtain ⟨j,hj,hilo,hjcut,hbit,hsuffix⟩ := rightmost_sound path skip selected.2
  rw [hi] at hj
  have he : i=j := Option.some.inj hj
  subst j
  have member := graph_leaf_member state path name leaf
  have walk : PreparedWalk path (.op name) :=
    expanded_leaf_follows traceState557.acc producerExpand (path,name) member
  have hcount : path.count false≤11 := (prepared_path_bound path (.op name) walk).2
  have hnextList : traceState557.acc.leaves.toList[dst]?=some (next,nextName) := by
    simpa only [Array.getElem?_toList] using hnext
  obtain ⟨bound,hget⟩ := List.getElem?_eq_some_iff.mp hnextList
  have hnextMem : (next,nextName) ∈ traceState557.acc.leaves.toList := by
    rw [←hget]
    exact List.getElem_mem bound
  have hnextWalk : PreparedWalk next (.op nextName) :=
    expanded_leaf_follows traceState557.acc producerExpand (next,nextName) hnextMem
  have hnextLength : next.length≤55 := (prepared_path_bound next (.op nextName) hnextWalk).1
  have hfirst : t origin=true := by
    obtain ⟨raw,heq,_⟩ := walk
    have hw := word
    rw [heq] at hw
    simpa [preparedPrefix,Holds] using hw.1
  have hanchor : t (origin+2)=false := by
    obtain ⟨raw,heq,_⟩ := walk
    have hw := word
    rw [heq] at hw
    simp only [preparedPrefix,List.cons_append,Holds] at hw
    have hh : origin+1+1=origin+2 := by omega
    simpa only [hh] using hw.2.2.1
  have hskipLen : skip≤path.length := by omega
  obtain ⟨steps,out,hsteps,hout,hleft,hgap,hsepout,hright,hbank,hsegment⟩ :=
    carry_produces_candidate_exact t origin h p separator path next skip i
      (next.length-(path.take i ++ [true]).length) hskipLen hpos hilo hjcut hbit hsuffix hshape
      (by omega) hcount word hfirst hanchor left hp hone between hsep ones blank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hnextWalk,hsteps,hout,hleft,hgap,hsepout,hright,hbank,hsegment⟩

/-- Original successor interface. -/
theorem carry_to_first_successor (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (increment : Bool) (operation : namedOperation name=some (n,increment))
    (skip : Nat) (hskip : skip=0 ∨ skip=1) (branch : skip=1 → increment=false)
    (t : Int → Bool) (origin h p separator : Int)
    (hpos : h=origin+((path.length-skip : Nat) : Int)-1)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (hp : h<p) (hone : t p=true)
    (between : ∀ q, h<q → q<p → t q=false) (hsep : p+1<separator)
    (ones : ∀ q, p<q → q<separator → t q=true) (blank : t separator=false) :
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path skip=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      PreparedWalk next (.op nextName) ∧ 0<steps ∧ Holds out origin next ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hw,hs,hword,_,_,_,hr,hbank,hseg⟩ := carry_to_first_successor_exact state path name leaf notRoot n increment operation skip hskip branch t origin h p separator hpos room word left hp hone between hsep ones blank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hw,hs,hword,hr,hbank,hseg⟩

#print axioms carry_to_first_successor_exact
#print axioms carry_to_first_successor
end Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
