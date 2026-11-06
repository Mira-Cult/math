import Shared.Beeping.NPcoNP.NativeHalf143ZeroReturn
import Shared.Beeping.NPcoNP.Grammar284SuccessorShape
import Shared.Beeping.NPcoNP.NativeCarryPivot
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch

/-! A supplied silent positive-HALF return composes with the literal carry to
the first expanded grammar successor under explicit path-shape assumptions. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfPositiveSuccessor
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalf143ZeroReturn
open Shared.Beeping.NPcoNP.NativeCarryPivot
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

theorem prepared_positive_to_first_successor (row : Fin 185) (dstIndex : Nat)
    (path : Path) (name : String) (skip : Nat) (hskip : skip≤1)
    (leaf : graphLeaf row=some (path,name))
    (hshape : successorShape path skip=true) (hrightmost : rightmostOK path skip=true)
    (hlast : path.getLast?=some false)
    (hsucc : successor traceState557.acc.starts path skip=some dstIndex)
    (origin h separator bound : Int) (t : Int → Bool) (bankWord : List Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (boundAfter : separator≤bound)
    (halfReturn : ∃ (steps : Nat) (mid : Int → Bool), 0<steps ∧
      (∀ q, q<h → mid q=t q) ∧ mid h=false ∧ mid (h+1)=false ∧ mid (h+2)=true ∧
      (∀ q, h+2<q → q<separator → mid q=true) ∧ mid separator=false ∧
      Holds mid (separator+1) bankWord ∧ (∀ q, bound≤q → mid q=false) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 1 (h-1-(skip : Int)) mid) steps) :
    ∃ (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      traceState557.acc.leaves[dstIndex]?=some (next,nextName) ∧ 0<steps ∧ Holds out origin next ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧ Holds out (separator+1) bankWord ∧
      (∀ q, bound≤q → out q=false) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨a,mid,ha,hframe,hzero,hz1,hmark,hones,hsep,hbank,hblank,hreturn⟩ := halfReturn
  have hmidword : Holds mid origin path := by
    apply holds_transport t mid origin path word
    intro q hq hq'
    exact (hframe q (by omega)).symm
  have hmidleft : ∀ q, q<origin → mid q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact left q hq
  have hlastword : path.dropLast ++ [false]=path :=
    List.dropLast_append_getLast? false (by simp [hlast])
  have hlastlen : path.dropLast.length+1=path.length := by
    have hh := congrArg List.length hlastword
    simpa using hh
  have hlastHold : Holds t origin (path.dropLast ++ [false]) := by rw [hlastword]; exact word
  obtain ⟨_,hlastTail⟩ := holds_split t origin path.dropLast [false] hlastHold
  have lastZero : t (h-1)=false := by
    have hh : t (origin+(path.dropLast.length : Int))=false := by simpa [Holds] using hlastTail
    have he : origin+(path.dropLast.length : Int)=h-1 := by omega
    simpa only [he] using hh
  have hmidlast : mid (h-1)=false := (hframe _ (by omega)).trans lastZero
  have hbetween : ∀ q, h-1-(skip : Int)<q → q<h+2 → mid q=false := by
    intro q hq hq'
    have he : q=h-1 ∨ q=h ∨ q=h+1 := by omega
    rcases he with rfl | rfl | rfl
    · exact hmidlast
    · exact hzero
    · exact hz1
  obtain ⟨i,dst,next,nextName,hi,hdst,hnext,hnextShape⟩ := successor_shape_sound path skip hshape
  obtain ⟨j,hj,hjlo,hjhi,hbit,hsuffix⟩ := rightmost_sound path skip hrightmost
  rw [hi] at hj
  have he : i=j := Option.some.inj hj
  subst j
  rw [hsucc] at hdst
  have hd : dst=dstIndex := (Option.some.inj hdst).symm
  subst dst
  have nlist : traceState557.acc.leaves.toList[dstIndex]?=some (next,nextName) := by
    simpa only [Array.getElem?_toList] using hnext
  obtain ⟨bound,hget⟩ := List.getElem?_eq_some_iff.mp nlist
  have nmem : (next,nextName) ∈ traceState557.acc.leaves.toList := by
    rw [←hget]
    exact List.getElem_mem bound
  have nwalk : PreparedWalk next (.op nextName) := expanded_leaf_follows traceState557.acc producerExpand (next,nextName) nmem
  have nlen : next.length≤55 := (prepared_path_bound next (.op nextName) nwalk).1
  have member := graph_leaf_member row path name leaf
  have walk : PreparedWalk path (.op name) := expanded_leaf_follows traceState557.acc producerExpand (path,name) member
  have count : path.count false≤11 := (prepared_path_bound path (.op name) walk).2
  have hfirst : mid origin=true := by
    obtain ⟨raw,he,_⟩ := walk
    have hw := hmidword
    rw [he] at hw
    simpa [preparedPrefix,Holds] using hw.1
  have hanchor : mid (origin+2)=false := by
    obtain ⟨raw,he,_⟩ := walk
    have hw := hmidword
    rw [he] at hw
    simp only [preparedPrefix,List.cons_append,Holds] at hw
    have hh : origin+1+1=origin+2 := by omega
    simpa only [hh] using hw.2.2.1
  obtain ⟨b,out,hb,hout,houtleft,houtgap,houtsep,houtmark,hbankFrame,hcarry⟩ :=
    carry_produces_candidate_exact mid origin (h-1-(skip : Int)) (h+2) separator path next skip i
      (next.length-(path.take i ++ [true]).length) (by omega) (by simp only [Nat.cast_sub (by omega : skip≤path.length)]; omega) hjlo hjhi hbit hsuffix hnextShape
      (by omega) count hmidword hfirst hanchor hmidleft (by omega) hmark hbetween (by omega) hones hsep
  have houtbank : Holds out (separator+1) bankWord := by
    apply holds_transport mid out (separator+1) _ hbank
    intro q hq _
    exact (hbankFrame q (by omega)).symm
  refine ⟨next,nextName,a+b,out,hnext,by omega,hout,houtleft,houtgap,houtsep,houtmark,houtbank,?_,
    segAdd machine _ _ _ a b hreturn hcarry⟩
  intro q hq
  rw [hbankFrame q (by omega)]
  exact hblank q hq

#print axioms prepared_positive_to_first_successor
end Shared.Beeping.NPcoNP.Grammar284HalfPositiveSuccessor
