import Shared.PNP.Record285.GrammarPath
import Shared.PNP.Record285.GrammarSuffix

/-! The byte-bound producer grammar's increment leaves refine to the literal
machine, on the explicit clean physical layout. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementReturn (atLeftWord)

/-- Every typed producer-grammar edge agrees with its literal physical row,
including continuation, break, half, decrement, and beep-control entries. -/
theorem producer_literal_edge (n : Nat) (b : Bool) (e : Edge)
    (h : nodeEdge n b = some e) :
    ∃ row, expected e b = some row ∧ Record285.machine.table.row (state n) b = row := by
  obtain ⟨row,he,hr⟩ := edge_verified n b e h
  exact ⟨row,he,by rw [ArtifactEndpoint.literal_rows]; exact hr⟩

/-- The frozen JSON binds the exact typed node graph, root and register list;
its root traversal and every final literal row are checked. -/
theorem literal_grammar_properties :
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    (∀ input : Nat → Bool, ∀ pos,
      ∃ e len, 0 < len ∧ len ≤ 163 ∧ isLeaf e = true ∧
        walk rootIndex (window input pos len) = some e) ∧
    (∀ code e, walk rootIndex code = some e →
      ∃ pre bit parent row, code = pre++[bit] ∧
        GenericDispatch.route GenericDispatch.treeRoot pre = some (state parent) ∧
        nodeEdge parent bit = some e ∧ expected e bit = some row ∧
        Record285.machine.table.row (state parent) bit = row) := by
  refine ⟨literal_typed_serialization,?_,?_⟩
  · intro input pos
    simpa only [rootIndex] using root_walk_terminates input pos
  · intro code e h
    exact root_final_edge code e (by simpa only [rootIndex] using h)

/-- A path in the typed data serialized exactly by the frozen producer JSON
selects the corresponding literal increment terminal. -/
theorem producer_increment_route (code : List Bool) (i : Nat)
    (hwalk : walk rootIndex code = some (.inc i)) :
    i < 15 ∧ GenericDispatch.route GenericDispatch.treeRoot code =
      some (IncrementPreparation.terminal i) :=
  root_increment_route code i (by simpa only [rootIndex] using hwalk)

/-- Every producer-grammar increment path, once placed in the explicit clean
tape layout, performs the selected increment and cleanup without events.
This does not yet prove the source program reaches that grammar path. -/
theorem producer_increment_physical (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementPreparation.terminal before.length,head,
      SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))⟩ physical) :
    let selected := gap::(before++[target])
    let n := (IncrementCleanup.peel (SymbolicDispatch.pathLeft code)).1
    let far := SymbolicDispatch.bits (IncrementCleanup.peel (SymbolicDispatch.pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    Rel (atLeftWord IncrementPreparation.dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*updated)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  obtain ⟨hi,hr⟩ := producer_increment_route code before.length hwalk
  exact DispatcherIncrement.all_routes_increment_physical gap target before suffix hi code hr
    head leftTail retained physical hrel

/-- The exact producer grammar bytes and the corresponding physical
increment contract, presented together without a text-binding premise. -/
theorem bound_producer_increment_physical (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementPreparation.terminal before.length,head,
      SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))⟩ physical) :
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    let selected := gap::(before++[target])
    let n := (IncrementCleanup.peel (SymbolicDispatch.pathLeft code)).1
    let far := SymbolicDispatch.bits (IncrementCleanup.peel (SymbolicDispatch.pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    Rel (atLeftWord IncrementPreparation.dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*updated)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps :=
  ⟨literal_typed_serialization, producer_increment_physical gap target before suffix code hwalk
    head leftTail retained physical hrel⟩

/-- The lexical carry remains inside the grammar path, preserving the root. -/
theorem producer_increment_preserves_root (code : List Bool) (i : Nat)
    (hwalk : walk rootIndex code = some (.inc i)) :
    IncrementCleanup.peel (SymbolicDispatch.pathLeft code) =
      ((IncrementCleanup.peel code.reverse).1,
        (IncrementCleanup.peel code.reverse).2 ++ [false,true,true] ++ List.replicate 6 false) := by
  obtain ⟨_,hr⟩ := producer_increment_route code i hwalk
  exact DispatcherIncrement.all_routes_preserve_root code i hr

end Shared.PNP.Record285.Grammar
