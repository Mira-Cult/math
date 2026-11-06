import Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
import Shared.Beeping.NPcoNP.Grammar284ControlSelector

/-! Audits a reachable selector boundary and repairs the synthetic padding
interface with an explicit continuation and unary zero reserve. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ControlSelector

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PathSelector
open Shared.Beeping.NPcoNP.Grammar284ControlSelector
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem returned_no_double_zero : ∀ i : Fin 68,
    ¬ (returnedTape (1-(i.val : Int))=false ∧ returnedTape (1-(i.val : Int)-1)=false) := by
  unfold returnedTape currentTape
  rw [run_2133586]
  decide

theorem down_append_tail (t : Int → Bool) (h : Int) (xs ys : List Bool)
    (hw : downHolds t h (xs++ys)) : downHolds t (h-(xs.length : Int)) ys := by
  induction xs generalizing h with
  | nil => simpa using hw
  | cons b xs ih =>
    simp only [List.cons_append,downHolds] at hw
    have ht := ih (h-1) hw.2
    have hp : h-1-(xs.length : Int)=h-((xs.length : Int)+1) := by omega
    simpa [Nat.cast_succ,hp] using ht

theorem padded_last_two (path : List Bool) (hz : path.count false≤11) :
    ∃ pre, paddedPath path=pre++[false,false] := by
  have hn : 14-path.count false = (14-path.count false-2)+2 := by omega
  refine ⟨path++List.replicate (14-path.count false-2) false, ?_⟩
  dsimp [paddedPath]
  conv_lhs => rw [hn,List.replicate_add]
  simp [List.append_assoc]

theorem returned_rejects_padded (path : List Bool) (last : Leaf)
    (hp : PreparedWalk path last) (rest : List Bool) :
    ¬ downHolds returnedTape 1 (paddedPath path++rest) := by
  intro hw
  have hz := (prepared_path_bound path last hp).2
  have hlen := (preparedPath_selector path last hp returnedTape 1 rest hw).2.1
  obtain ⟨pre,he⟩ := padded_last_two path hz
  have hprefix : pre.length+2≤68 := by
    rw [he] at hlen
    simp at hlen
    omega
  have htail : downHolds returnedTape (1-(pre.length : Int)) ([false,false]++rest) := by
    apply down_append_tail returnedTape 1 pre
    simpa [he,List.append_assoc] using hw
  simp only [List.cons_append,List.nil_append,downHolds] at htail
  have hnot := returned_no_double_zero ⟨pre.length,by omega⟩
  exact hnot ⟨htail.1,htail.2.1⟩

#print axioms returned_rejects_padded

/-- The previously checked blank-start run really visits state 83 at the
head and tape used in the padding counterexample. -/
theorem actual_state83 : machine.system.run 2133593 = cfg 83 1 returnedTape := by
  have h0 : currentTape (-2)=false := zero_neg2
  have hother (p : Int) (hp : p≠ -2) : setAt (-2) currentTape p=currentTape p := by
    simp only [setAt,if_neg hp]
  have h1 : setAt (-2) currentTape (-1)=false := by
    rw [hother (-1) (by decide)]
    exact zero_neg1
  have hz : ∀ i : Nat, i<3 → setAt (-2) currentTape (0+(i : Int))=false := by
    intro i hi
    have hi' : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi' with rfl | rfl | rfl
    · change setAt (-2) currentTape 0=false
      rw [hother 0 (by decide)]
      exact zero_0
    · change setAt (-2) currentTape 1=false
      rw [hother 1 (by decide)]
      exact zero_1
    · change setAt (-2) currentTape 2=false
      rw [hother 2 (by decide)]
      exact zero_2
  have hm : setAt (-2) currentTape (0+(3 : Int))=true := by
    change setAt (-2) currentTape 3=true
    rw [hother 3 (by decide)]
    exact one_3
  have hfirst := oneSeg machine _ _ (step261_zero (-2) currentTape h0)
  have hsecond := oneSeg machine _ _ (step42_zero (-1) (setAt (-2) currentTape) h1)
  have hdispatch : silentSegment machine (cfg 261 (-2) currentTape)
      (cfg 10 0 (setAt (-2) currentTape)) 2 := by
    simpa using segAdd machine _ _ _ 1 1 hfirst hsecond
  have hscan : silentSegment machine (cfg 10 0 (setAt (-2) currentTape))
      (cfg 83 1 returnedTape) 5 := by
    simpa only [returnedTape,Int.zero_add,Nat.cast_ofNat,Int.reduceSub,Nat.reduceAdd] using
      scan10_return83 3 0 (setAt (-2) currentTape) (by decide) hz hm
  have hc : machine.system.run 2133586 = cfg 261 (-2) currentTape := by
    have hs := state261
    have hh := head_neg2
    cases he : machine.system.run 2133586 with
    | mk state head tape =>
      simp only [he,cfg] at hs hh ⊢
      simp only [currentTape,he,cfg] at *
      cases hs
      cases hh
      rfl
  have hseven : silentSegment machine (machine.system.run 2133586) (cfg 83 1 returnedTape) 7 := by
    rw [hc]
    simpa using segAdd machine _ _ _ 2 5 hdispatch hscan
  have hblank : silentSegment machine (machine.system.run 0) (cfg 83 1 returnedTape) 2133593 := by
    have h := segAdd machine _ _ _ 2133586 7 blank_start_66 (by
      rw [← run_2133586]
      exact hseven)
    simpa using h
  exact run_of_initial_segment 2133593 _ hblank

theorem actual_state83_rejects_padded (path : List Bool) (last : Leaf)
    (hp : PreparedWalk path last) (rest : List Bool) :
    ¬ downHolds (machine.system.run 2133593).tape
      (machine.system.run 2133593).head (paddedPath path++rest) := by
  rw [actual_state83]
  exact returned_rejects_padded path last hp rest

#print axioms actual_state83_rejects_padded

/-- A literal factorization of the observed descending word. It does not
claim that this prefix is the current source graph program counter. -/
def observedPath : List Bool := [true,true,false,true,false,true]
def observedContinuation : List Bool := [true,false]

theorem observed_path_valid : PreparedWalk observedPath (.op "_continue.1") := by
  have h : follow producerGrammar (.node producerGrammar.root) [true,false,true] =
      some (.op "_continue.1") := by decide
  exact ⟨[true,false,true],rfl,follow_sound producerGrammar _ _ _ h⟩

theorem observed_word : controlWord observedPath observedContinuation = blocks selectorCounts := by decide

theorem observed_budget : (observedPath++observedContinuation).count false≤13 := by decide

theorem observed_selector :
    silentSegment machine (machine.system.run 2133593) (cfg 92 (-29) returnedTape) 30 := by
  have hw : downHolds returnedTape 1 (controlWord observedPath observedContinuation ++ []) := by
    rw [observed_word]
    simpa using selector_input
  have hs := (controlWord_selector observedPath observedContinuation observed_budget returnedTape 1 [] hw).2.2
  rw [actual_state83]
  have hlen : (controlWord observedPath observedContinuation).length=30 := by
    rw [observed_word,selector_bits_length]
  simpa only [hlen,Nat.cast_ofNat,Int.reduceSub] using hs

#print axioms observed_path_valid
#print axioms observed_word
#print axioms observed_selector

open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace

theorem observed_expanded_leaf :
    (observedPath,"_continue.1") ∈ traceState557.acc.leaves.toList := by decide

#print axioms observed_expanded_leaf

/-- The observed finite word instantiates the expansion-leaf selector theorem.
The proof does not identify this syntactic leaf with a graph execution state. -/
theorem observed_expanded_selector :
    PreparedWalk observedPath (.op "_continue.1") ∧
    silentSegment machine (machine.system.run 2133593) (cfg 92 (-29) returnedTape) 30 := by
  have hw : downHolds returnedTape 1 (controlWord observedPath observedContinuation ++ []) := by
    rw [observed_word]
    simpa using selector_input
  have hs := expanded_leaf_control_selector traceState557.acc producerExpand
    (observedPath,"_continue.1") observed_expanded_leaf observedContinuation observed_budget returnedTape 1 [] hw
  refine ⟨hs.1,?_⟩
  have hlen : (controlWord observedPath observedContinuation).length=30 := by
    rw [observed_word,selector_bits_length]
  rw [actual_state83]
  simpa only [hlen,Nat.cast_ofNat,Int.reduceSub] using hs.2.2.2

#print axioms observed_expanded_selector

end Shared.Beeping.NPcoNP.Bootstrap284ControlSelector
