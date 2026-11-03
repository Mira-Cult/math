import Shared.PNP.Record285.GrammarRootDispatch

/-! Relate the physical lexical carry to the producer's skip-zero successor
rule on control paths, without assuming the next source instruction. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup

/-- Scan the path from right to left, discard trailing ones, and turn the
first zero into a one. This is the skip-zero rule in the producer's
`shared/test_occurrences.py`; no checked translation of that Python is claimed. -/
def returnAfterZero : List Bool → Option (List Bool)
  | [] => none
  | false::rest => some (rest.reverse ++ [true])
  | true::rest => returnAfterZero rest

def returnPath (code : List Bool) : Option (List Bool) := returnAfterZero code.reverse

theorem return_after_zero (xs : List Bool) (hasZero : false ∈ xs) :
    returnAfterZero xs = some ((peel xs).2.reverse ++ [true]) := by
  induction xs with
  | nil => simp at hasZero
  | cons b bs ih =>
    cases b with
    | false => simp [returnAfterZero,peel]
    | true =>
      have hz : false ∈ bs := by simpa using hasZero
      simpa only [returnAfterZero,peel] using ih hz

theorem peel_decomposition (xs : List Bool) (hasZero : false ∈ xs) :
    xs = List.replicate (peel xs).1 true ++ false::(peel xs).2 := by
  induction xs with
  | nil => simp at hasZero
  | cons b bs ih =>
    cases b with
    | false => simp [peel]
    | true =>
      have hz : false ∈ bs := by simpa using hasZero
      have h := ih hz
      cases hp : peel bs with
      | mk n rest =>
        simp only [hp] at h
        simp only [peel,hp,List.replicate_succ,List.cons_append]
        exact congrArg (List.cons true) h

/-- Every grammar increment route has a rightmost zero inside its path. Its
physical cleanup flips that zero and removes exactly the trailing ones. -/
theorem increment_return_path (code : List Bool) (i : Nat)
    (hwalk : walk rootIndex code = some (.inc i)) :
    let p := peel code.reverse
    let successor := p.2.reverse ++ [true]
    returnPath code = some successor ∧
    code = p.2.reverse ++ [false] ++ List.replicate p.1 true ∧
    code.length = successor.length+p.1 := by
  have hr := (producer_increment_route code i hwalk).2
  have hz : false ∈ code := DispatcherIncrement.route_has_zero code i hr
  have hzrev : false ∈ code.reverse := by simpa using hz
  have hp := return_after_zero code.reverse hzrev
  have hd := peel_decomposition code.reverse hzrev
  have hh := congrArg List.reverse hd
  simp only [List.reverse_reverse,List.reverse_append,List.reverse_cons,
    List.reverse_replicate] at hh
  dsimp only
  refine ⟨hp,?_,?_⟩
  · simpa only [List.append_assoc,List.singleton_append] using hh
  · have hlen := congrArg List.length hh
    simp only [List.length_append,List.length_replicate,
      List.length_reverse,List.length_cons,List.length_nil] at hlen ⊢
    omega

/-- The physical cleanup marker is at the final position of the producer's
new control prefix, measured from the same dispatcher-root position. -/
theorem increment_return_head (code : List Bool) (i : Nat)
    (hwalk : walk rootIndex code = some (.inc i)) (head : Int) :
    let p := peel code.reverse
    let successor := p.2.reverse ++ [true]
    head-(p.1:Int)-1 = head-(code.length:Int)+(successor.length:Int)-1 := by
  have h := (increment_return_path code i hwalk).2.2
  dsimp only at h ⊢
  omega

/-- The cleanup's actual peeled tape has the same carry length and retained
prefix as the grammar successor, and its marker is at that prefix's end. -/
theorem increment_cleanup_control (code : List Bool) (i : Nat)
    (hwalk : walk rootIndex code = some (.inc i)) (head : Int) :
    let p := peel code.reverse
    let successor := p.2.reverse ++ [true]
    returnPath code = some successor ∧
    (peel (SymbolicDispatch.pathLeft code)).1 = p.1 ∧
    (peel (SymbolicDispatch.pathLeft code)).2 =
      p.2 ++ [false,true,true] ++ List.replicate 6 false ∧
    head-(p.1:Int)-1 = head-(code.length:Int)+(successor.length:Int)-1 := by
  have hp := producer_increment_preserves_root code i hwalk
  have hf := congrArg Prod.fst hp
  have hs := congrArg Prod.snd hp
  exact ⟨(increment_return_path code i hwalk).1,hf,hs,increment_return_head code i hwalk head⟩

/-- The byte-bound grammar path, actual physical increment and cleanup, and
the producer's skip-zero control prefix in one theorem. The next leaf after
that prefix and its source-level interpretation remain separate obligations. -/
theorem bound_root_increment_with_successor (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained)))) physical) :
    let p := peel code.reverse
    let successor := p.2.reverse ++ [true]
    let selected := gap::(before++[target])
    let n := (peel (SymbolicDispatch.pathLeft code)).1
    let far := SymbolicDispatch.bits (peel (SymbolicDispatch.pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := code.length + ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    returnPath code = some successor ∧ n = p.1 ∧
    (peel (SymbolicDispatch.pathLeft code)).2 =
      p.2 ++ [false,true,true] ++ List.replicate 6 false ∧
    head-(p.1:Int)-1 = head-(code.length:Int)+(successor.length:Int)-1 ∧
    Rel (atLeftWord IncrementPreparation.dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*updated)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hc := increment_cleanup_control code before.length hwalk head
  have hp := root_through_increment_physical gap target before suffix code hwalk head leftTail retained physical hrel
  exact ⟨literal_typed_serialization,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,hp.1,hp.2.1,hp.2.2⟩

end Shared.PNP.Record285.Grammar
