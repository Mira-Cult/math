import Shared.PNP.Record285.DecrementZeroCleanup
import Shared.PNP.Record285.GrammarBeepUnique

/-! Control-word facts for the zero branch of every producer decrement. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariant (detector_append)

theorem all_true_replicate (xs : List Bool) (h : false ∉ xs) :
    xs = List.replicate xs.length true := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => simp at h
    | true =>
      have hh : false ∉ bs := by simpa using h
      have he := congrArg (List.cons true) (ih hh)
      simpa only [List.length_cons,List.replicate_succ] using he

theorem replicate_add (a b : Nat) :
    List.replicate (a+b) true = List.replicate a true ++ List.replicate b true := by
  induction a with
  | zero => simp
  | succ a ih =>
    simpa only [Nat.succ_add,List.replicate_succ,List.cons_append] using
      congrArg (List.cons true) ih

theorem false_split (xs : List Bool) (h : false ∈ xs) :
    ∃ pre post, xs = pre++false::post := by
  induction xs with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | false => exact ⟨[],bs,rfl⟩
    | true =>
      have hh : false ∈ bs := by simpa using h
      obtain ⟨pre,post,hp⟩ := ih hh
      exact ⟨true::pre,post,by simpa only [List.cons_append] using congrArg (List.cons true) hp⟩

theorem true_tail_no_decrement (n i : Nat) :
    walk 159 (List.replicate n true) ≠ some (.dec i) := by
  have hchain (rest : List Bool) :
      walk 159 ([true,true,true,true,true,true,true]++rest) =
        if rest.isEmpty then some (.inc 6) else none := by
    cases rest <;> simp [walk,nodeEdge,nodes_fast,fastNodes]
  by_cases hsmall : n < 7
  · have hc : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [walk,nodeEdge,nodes_fast,fastNodes,List.replicate]
  · have hn : n = 7+(n-7) := by omega
    rw [hn,replicate_add]
    change walk 159 ([true,true,true,true,true,true,true]++List.replicate (n-7) true) ≠ _
    rw [hchain]
    split <;> simp

/-- Every complete decrement path has two zeros in its own word. -/
theorem decrement_two_zeros (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.dec i)) :
    ∃ pre mid post, code = pre++[false]++mid++[false]++post := by
  cases code with
  | nil => simp [walk] at hwalk
  | cons a as =>
    cases a with
    | false => cases as <;> simp [walk,root_false_edge] at hwalk
    | true =>
      cases as with
      | nil => simp [walk,root_true_edge] at hwalk
      | cons b bs =>
        cases b with
        | true => cases bs <;> simp [walk,root_true_edge,next_true_edge] at hwalk
        | false =>
          cases bs with
          | nil => simp [walk,root_true_edge,next_false_edge] at hwalk
          | cons c cs =>
            cases c with
            | false => exact ⟨[true],[],cs,by simp⟩
            | true =>
              have htail : walk 159 cs = some (.dec i) := by
                simpa only [walk,root_true_edge,next_false_edge,beep_true_edge] using hwalk
              have hz : false ∈ cs := by
                by_cases hn : false ∈ cs
                · exact hn
                · have ht := all_true_replicate cs hn
                  rw [ht] at htail
                  exact False.elim ((true_tail_no_decrement cs.length i) htail)
              obtain ⟨pre,post,h⟩ := false_split cs hz
              refine ⟨[true],true::pre,post,?_⟩
              simp [h,List.append_assoc]

theorem peel_tail_zero_of_two (pre mid post : List Bool) :
    false ∈ (peel (pre++[false]++mid++[false]++post)).2 := by
  induction pre with
  | nil => simp [peel]
  | cons b bs ih =>
    cases b with
    | false => simp [peel]
    | true => simpa only [List.cons_append,peel] using ih

theorem decrement_reverse_zeros (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.dec i)) :
    false ∈ code.reverse ∧ false ∈ (peel code.reverse).2 := by
  obtain ⟨pre,mid,post,hcode⟩ := decrement_two_zeros code i hwalk
  have hrev : code.reverse = post.reverse++[false]++mid.reverse++[false]++pre.reverse := by
    simp [hcode,List.reverse_append,List.append_assoc]
  rw [hrev]
  exact ⟨by simp,peel_tail_zero_of_two post.reverse mid.reverse pre.reverse⟩

/-- The zero-case return skips one zero, then changes the next zero to one. -/
def returnAfterOneSkip : List Bool → Option (List Bool)
  | [] => none
  | false::rest => returnAfterZero rest
  | true::rest => returnAfterOneSkip rest

def returnPathSkipOne (code : List Bool) : Option (List Bool) :=
  returnAfterOneSkip code.reverse

theorem return_after_one_skip (xs : List Bool) (hz : false ∈ xs)
    (ht : false ∈ (peel xs).2) :
    returnAfterOneSkip xs = some ((peel (peel xs).2).2.reverse++[true]) := by
  induction xs with
  | nil => simp at hz
  | cons b bs ih =>
    cases b with
    | false => simpa only [returnAfterOneSkip,peel] using return_after_zero bs ht
    | true =>
      have hz' : false ∈ bs := by simpa using hz
      have ht' : false ∈ (peel bs).2 := by simpa only [peel] using ht
      simpa only [returnAfterOneSkip,peel] using ih hz' ht'

theorem peel_prefix_safe (code : List Bool)
    (hsafe : detectorRun 0 (scanWord code) = some 0) (hz : false ∈ code.reverse) :
    detectorRun 0 (scanWord ((peel code.reverse).2.reverse)) = some 0 := by
  have hd := peel_decomposition code.reverse hz
  have hs' : detectorRun 0
      ((List.replicate (peel code.reverse).1 true ++ false::(peel code.reverse).2) ++
        [false,true,true]) = some 0 := by
    rw [← hd]
    exact hsafe
  rw [List.append_assoc,detector_append,detector_true_run] at hs'
  change detectorRun 1 ((peel code.reverse).2 ++ [false,true,true]) = some 0 at hs'
  obtain ⟨d,hd,hbound⟩ := detector_run_mono
    ((peel code.reverse).2++[false,true,true]) 0 1 0 (by omega) hs'
  have : d=0 := by omega
  subst d
  simpa only [scanWord,List.reverse_reverse] using hd

/-- Both zero skips stay within the producer word; the frozen root and its
margin survive, and the returned prefix is the skip-one source rule. -/
theorem decrement_control_preserves_root (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.dec i)) :
    let p := peel code.reverse
    let q := peel p.2
    peel (pathLeft code) = (p.1,p.2++rootLeft) ∧
    peel (peel (pathLeft code)).2 = (q.1,q.2++rootLeft) ∧
    returnPathSkipOne code = some (q.2.reverse++[true]) ∧
    detectorRun 0 (scanWord q.2.reverse) = some 0 := by
  obtain ⟨hz,ht⟩ := decrement_reverse_zeros code i hwalk
  have hzcode : false ∈ code := by simpa using hz
  have hp := IncrementCleanup.path_peel_preserves_root code hzcode
  have hp' : peel (pathLeft code) =
      ((peel code.reverse).1,(peel code.reverse).2++rootLeft) := by
    simpa only [rootLeft,List.append_assoc] using hp
  have hq := IncrementCleanup.peel_append (peel code.reverse).2 rootLeft ht
  have hq' : peel (peel (pathLeft code)).2 =
      ((peel (peel code.reverse).2).1,(peel (peel code.reverse).2).2++rootLeft) := by
    rw [hp']
    exact hq
  have hr := return_after_one_skip code.reverse hz ht
  obtain ⟨_,_,hsafe⟩ := producer_decrement_safe code i hwalk
  have hs1 := peel_prefix_safe code hsafe hz
  have hz1 : false ∈ ((peel code.reverse).2.reverse).reverse := by simpa using ht
  have hs2 := peel_prefix_safe (peel code.reverse).2.reverse hs1 hz1
  simp only [List.reverse_reverse] at hs2
  exact ⟨hp',hq',hr,hs2⟩

end Shared.PNP.Record285.Grammar
