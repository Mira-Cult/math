import Shared.PNP.Record285.ProjectionEndpoint
import Shared.PNP.Record285.SourceControllerSimulation

/-! Identify the control states visited inside a contracted-move expansion.
This supports aligning search-controller boundaries with exact logical actions. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.ExpansionBoundary
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore

/-- Every proper-prefix state of a primitive move loop is at its actual
head or body row, including all iterations and the zero case. -/
theorem expanded_move_inside (rows : Array Row) (head body exit src dst n : Nat) (bank : Nat → Nat)
    (hhead : rows[head]? = some ⟨.dec src,body,exit⟩)
    (hbody : rows[body]? = some ⟨.inc dst,head,head⟩)
    (hne : src ≠ dst) (hvalue : bank src = n) (t : Nat) (ht : t < 2*n+1) :
    ((system rows).advance ⟨head,bank⟩ t).index = head ∨
      ((system rows).advance ⟨head,bank⟩ t).index = body := by
  induction n generalizing bank t with
  | zero =>
    have ht0 : t = 0 := by omega
    subst t
    exact Or.inl rfl
  | succ n ih =>
    by_cases hsmall : t < 2
    · have hcases : t = 0 ∨ t = 1 := by omega
      rcases hcases with rfl | rfl
      · exact Or.inl rfl
      · have hpos : bank src ≠ 0 := by omega
        have hs : step rows ⟨head,bank⟩ = (⟨body,update (.dec src) bank⟩,false) := by
          simp [step,hhead,observe,hpos]
        change (step rows ⟨head,bank⟩).1.index = head ∨
          (step rows ⟨head,bank⟩).1.index = body
        rw [hs]
        exact Or.inr rfl
    · let mid := expandedCycle src dst bank
      have hpos : 0 < bank src := by omega
      have hcycle := expandedCycle_run rows head body exit src dst bank hhead hbody hpos
      have hmid : mid src = n := by
        have h := expandedCycle_read src dst src bank hne
        simp only [if_true] at h
        change expandedCycle src dst bank src = n
        omega
      have htime : t = 2+(t-2) := by omega
      have hbound : t-2 < 2*n+1 := by omega
      rw [htime,advance_add,hcycle.1]
      exact ih mid hmid (t-2) hbound

/-- The frozen finite tables certify that a contracted-move loop cannot
visit either source-controller boundary row 1 or 6. -/
def markerSafeRow (i : Nat) : Bool :=
  match logicalRows[i]?, expansionMap[i]? with
  | some row, some pc =>
    match row.action with
    | .move _ _ =>
      match expandedRows[pc]? with
      | some target => decide (pc ≠ 1 ∧ pc ≠ 6 ∧ target.no ≠ 1 ∧ target.no ≠ 6)
      | none => false
    | _ => true
  | _, _ => false

def markersSafe : Bool := (List.range logicalRows.size).all markerSafeRow

theorem markers_safe : markersSafe = true := by decide

theorem move_markers_safe (i pc : Nat) (row target : Row)
    (hi : i < logicalRows.size) (hrow : logicalRows[i]? = some row)
    (hpc : expansionMap[i]? = some pc) (htarget : expandedRows[pc]? = some target)
    (src dst : Nat) (hmove : row.action = .move src dst) :
    pc ≠ 1 ∧ pc ≠ 6 ∧ target.no ≠ 1 ∧ target.no ≠ 6 := by
  have h := List.all_eq_true.mp markers_safe i (List.mem_range.mpr hi)
  simpa [markersSafe,markerSafeRow,hrow,hpc,hmove,htarget] using h

end Shared.PNP.Record285.ExpansionBoundary

namespace Shared.PNP.Record285.ExpansionBoundary
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore

def exactDuration (s : State) : Nat :=
  match logicalRows[s.index]? with
  | some row => match row.action with
    | .move src _ => 2*s.bank src+1
    | _ => 1
  | none => 1

/-- The checked move expansion has this exact, computable duration; all other
actions take one primitive transition. -/
theorem exact_progress (s p : State) (hrel : ExpansionRel logicalRows expansionMap s p) :
    0 < exactDuration s ∧
      ExpansionRel logicalRows expansionMap (step logicalRows s).1
        ((system expandedRows).advance p (exactDuration s)) ∧
      ((step logicalRows s).2 = true ↔
        ∃ j, j < exactDuration s ∧ (system expandedRows).BeepFrom p j) ∧
      ∀ j k, j < exactDuration s → k < exactDuration s →
        (system expandedRows).BeepFrom p j → (system expandedRows).BeepFrom p k → j = k := by
  have hi := hrel.1
  have hp := hrel.2.1
  obtain ⟨row,hrow⟩ : ∃ row, logicalRows[s.index]? = some row := ⟨logicalRows[s.index],by simp⟩
  have hrowcheck := (expansion_parts logicalRows expandedRows expansionMap expansion_checked).2.2 s.index hi
  obtain ⟨target,no,yes,htarget,hno,hyes,hmatch⟩ :=
    expansionRow_sound logicalRows expandedRows expansionMap s.index p.index row hrow hp hrowcheck
  cases ha : row.action with
  | move src dst =>
    have hbody : ∃ body, expandedRows[target.no]? = some body ∧ src ≠ dst ∧ target.action = .dec src ∧
        target.yes = no ∧ row.no = row.yes ∧ body.action = .inc dst ∧ body.no = p.index ∧ body.yes = p.index := by
      simpa [ExpansionMatch,ha] using hmatch
    obtain ⟨body,hbody,hne,hedge,hexit,_,hbodyEdge,hbodyNo,hbodyYes⟩ := hbody
    obtain ⟨hnext,hnoevent,hquiet⟩ := contracted_move_progress logicalRows expandedRows expansionMap expansion_checked s p hrel
      row target body no src dst hrow htarget hbody hno ha hne hedge hexit hbodyEdge hbodyNo hbodyYes
    simp only [exactDuration,hrow,ha]
    refine ⟨by omega,hnext,?_,?_⟩
    · constructor
      · intro he
        rw [hnoevent] at he
        contradiction
      · rintro ⟨j,hj,he⟩
        exact False.elim (hquiet j hj he)
    · intro j k hj hk he _
      exact False.elim (hquiet j hj he)
  | inc idx | dec idx | half idx | beep =>
    have hordinary : target.action = row.action ∧ target.no = no ∧ target.yes = yes := by
      simpa [ExpansionMatch,ha] using hmatch
    have hstep := ordinary_progress logicalRows expandedRows expansionMap expansion_checked s p hrel row target no yes
      hrow htarget hno hyes hordinary.1 hordinary.2.1 hordinary.2.2
    simp only [exactDuration,hrow,ha]
    refine ⟨by decide,hstep.1,?_,?_⟩
    · constructor
      · intro he
        exact ⟨0,by decide,by simpa [EventSystem.BeepFrom,EventSystem.advance,system] using hstep.2.symm.trans he⟩
      · rintro ⟨j,hj,he⟩
        have hz : j = 0 := by omega
        subst j
        have he' : (step expandedRows p).2 = true := by simpa [EventSystem.BeepFrom,EventSystem.advance,system] using he
        exact hstep.2.trans he'
    · intro j k hj hk _ _
      omega

noncomputable def exactSimulation : SegmentSimulation (system logicalRows) (system expandedRows) where
  Rel := ExpansionRel logicalRows expansionMap
  initial := expansion_initial logicalRows expandedRows expansionMap expansion_checked (by decide)
  duration := fun s _ => exactDuration s
  positive := fun s p h => (exact_progress s p h).1
  next := fun s p h => (exact_progress s p h).2.1
  event_iff := fun s p h => (exact_progress s p h).2.2.1
  event_unique := fun s p h => (exact_progress s p h).2.2.2

noncomputable def exactRefinement : EventRefinement (system logicalRows) (system expandedRows) :=
  exactSimulation.toEventRefinement

end Shared.PNP.Record285.ExpansionBoundary

namespace Shared.PNP.Record285.ExpansionBoundary
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore

/-- A visit to either controller boundary row is an exact logical-action
boundary, never the interior of a contracted move loop. -/
theorem marker_is_exact_boundary (n : Nat)
    (hmarker : ((system expandedRows).run n).index = 1 ∨
      ((system expandedRows).run n).index = 6) :
    ∃ j, n = exactRefinement.boundary j := by
  let r := exactRefinement
  obtain ⟨j,hlo,hhi⟩ := r.covers n
  let s := (system logicalRows).run j
  let p := (system expandedRows).run (r.boundary j)
  let t := n-r.boundary j
  have hn : n = r.boundary j+t := by dsimp [t]; omega
  have hbound : r.boundary (j+1) = r.boundary j + exactDuration s := by rfl
  have ht : t < exactDuration s := by rw [hbound] at hhi; omega
  have hrel : ExpansionRel logicalRows expansionMap s p := r.related j
  have hmark : ((system expandedRows).advance p t).index = 1 ∨
      ((system expandedRows).advance p t).index = 6 := by
    rw [hn,EventSystem.run_add] at hmarker
    exact hmarker
  have hi : s.index < logicalRows.size := hrel.1
  obtain ⟨row,hrow⟩ : ∃ row, logicalRows[s.index]? = some row := ⟨logicalRows[s.index],by simp⟩
  cases ha : row.action with
  | move src dst =>
    have hrowcheck := (expansion_parts logicalRows expandedRows expansionMap expansion_checked).2.2 s.index hrel.1
    obtain ⟨target,no,yes,htarget,hno,hyes,hmatch⟩ :=
      expansionRow_sound logicalRows expandedRows expansionMap s.index p.index row hrow hrel.2.1 hrowcheck
    have hsafety := move_markers_safe s.index p.index row target hrel.1 hrow hrel.2.1 htarget src dst ha
    have hbody : ∃ body, expandedRows[target.no]? = some body ∧ src ≠ dst ∧
        target.action = .dec src ∧ target.yes = no ∧ row.no = row.yes ∧
        body.action = .inc dst ∧ body.no = p.index ∧ body.yes = p.index := by
      simpa [ExpansionMatch,ha] using hmatch
    obtain ⟨body,hbody,hne,hedge,hexit,_,hbodyEdge,hbodyNo,hbodyYes⟩ := hbody
    have hhead' : expandedRows[p.index]? = some ⟨.dec src,target.no,no⟩ := by
      rw [logical_row_equal target _ _ _ hedge rfl hexit] at htarget
      exact htarget
    have hbody' : expandedRows[target.no]? = some ⟨.inc dst,p.index,p.index⟩ := by
      rw [logical_row_equal body _ _ _ hbodyEdge hbodyNo hbodyYes] at hbody
      exact hbody
    have ht' : t < 2*s.bank src+1 := by simpa [exactDuration,hrow,ha] using ht
    have hb : p.bank src = s.bank src := by rw [hrel.2.2]
    have hinside := expanded_move_inside expandedRows p.index target.no no src dst (s.bank src)
      p.bank hhead' hbody' hne hb t ht'
    have hp : (⟨p.index,p.bank⟩ : State) = p := by cases p; rfl
    rw [hp] at hinside
    rcases hinside with hhead | hbody
    · rcases hmark with hm | hm <;> rw [hhead] at hm <;> simp_all
    · rcases hmark with hm | hm <;> rw [hbody] at hm <;> simp_all
  | inc idx | dec idx | half idx | beep =>
    have ht0 : t = 0 := by simp [exactDuration,hrow,ha] at ht; omega
    refine ⟨j,?_⟩
    simpa [ht0] using hn

end Shared.PNP.Record285.ExpansionBoundary

namespace Shared.PNP.Record285.ExpansionBoundary
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore

/-- Every source-controller action boundary coincides with a logical-graph
action boundary under the exact ownership expansion. This records full-bank
projection and the source relation at the same graph state. -/
theorem source_boundary_is_logical_boundary (i : Nat) :
    let r := SourceControllerSimulation.simulation.toEventRefinement
    let n := 1+r.boundary i
    ∃ j, n = exactRefinement.boundary j ∧
      SourceControllerSimulation.Rel (Source.controller.run i)
        (SourceControllerSimulation.shiftedGraph.run (r.boundary i)) ∧
      RegisterProjection.Rel RegisterProjection.lift expandedRows
        ((system RegisterProjection.originalRows).run n) ((system expandedRows).run n) ∧
      ExpansionRel logicalRows expansionMap ((system logicalRows).run j) ((system expandedRows).run n) := by
  let r := SourceControllerSimulation.simulation.toEventRefinement
  let n := 1+r.boundary i
  have hsource := r.related i
  have hindex := hsource.2.2
  have hg : (SourceControllerSimulation.shiftedGraph.run (r.boundary i)).index = 1 ∨
      (SourceControllerSimulation.shiftedGraph.run (r.boundary i)).index = 6 := by
    by_cases hphase : (Source.controller.run i).phase = .begin
    · left
      simpa [hphase] using hindex
    · right
      simpa [hphase] using hindex
  have horig : ((system RegisterProjection.originalRows).run n).index = 1 ∨
      ((system RegisterProjection.originalRows).run n).index = 6 := by
    simpa [n,SourceControllerSimulation.shifted_run] using hg
  have hproj := RegisterProjection.related_run n
  have hexpanded : ((system expandedRows).run n).index = 1 ∨
      ((system expandedRows).run n).index = 6 := by
    rw [←hproj.1]
    exact horig
  obtain ⟨j,hj⟩ := marker_is_exact_boundary n hexpanded
  refine ⟨j,hj,hsource,hproj,?_⟩
  change ExpansionRel logicalRows expansionMap ((system logicalRows).run j) ((system expandedRows).run n)
  rw [hj]
  exact exactRefinement.related j

end Shared.PNP.Record285.ExpansionBoundary

namespace Shared.PNP.Record285.ExpansionBoundary
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore

theorem source_marker_preimage_one :
    ∀ i : Fin expansionMap.size, expansionMap[i.val]? = some 1 → i.val = 1 := by decide

theorem source_marker_preimage_six :
    ∀ i : Fin expansionMap.size, expansionMap[i.val]? = some 6 → i.val = 6 := by decide

/-- The aligned logical state itself is at the corresponding source boundary
row; the frozen expansion map has no other preimage for either marker. -/
theorem source_boundary_logical_marker (i : Nat) :
    let r := SourceControllerSimulation.simulation.toEventRefinement
    let n := 1+r.boundary i
    ∃ j, n = exactRefinement.boundary j ∧
      (((system logicalRows).run j).index = 1 ∨ ((system logicalRows).run j).index = 6) ∧
      SourceControllerSimulation.Rel (Source.controller.run i)
        (SourceControllerSimulation.shiftedGraph.run (r.boundary i)) ∧
      RegisterProjection.Rel RegisterProjection.lift expandedRows
        ((system RegisterProjection.originalRows).run n) ((system expandedRows).run n) ∧
      ExpansionRel logicalRows expansionMap ((system logicalRows).run j) ((system expandedRows).run n) := by
  dsimp only
  obtain ⟨j,hj,hsource,hproj,hexp⟩ := source_boundary_is_logical_boundary i
  let n := 1+SourceControllerSimulation.simulation.toEventRefinement.boundary i
  let idx := ((system logicalRows).run j).index
  have hn : ((system expandedRows).run n).index = 1 ∨ ((system expandedRows).run n).index = 6 := by
    have hidx := hsource.2.2
    have hg : (SourceControllerSimulation.shiftedGraph.run
        (SourceControllerSimulation.simulation.toEventRefinement.boundary i)).index = 1 ∨
        (SourceControllerSimulation.shiftedGraph.run
        (SourceControllerSimulation.simulation.toEventRefinement.boundary i)).index = 6 := by
      by_cases hp : (Source.controller.run i).phase = .begin
      · left; simpa [hp] using hidx
      · right; simpa [hp] using hidx
    have ho : ((system RegisterProjection.originalRows).run n).index = 1 ∨
        ((system RegisterProjection.originalRows).run n).index = 6 := by
      simpa [n,SourceControllerSimulation.shifted_run] using hg
    rw [←hproj.1]
    exact ho
  have hsize : idx < expansionMap.size := by
    have h := hexp.1
    rw [(expansion_parts logicalRows expandedRows expansionMap expansion_checked).1] at h
    exact h
  have hm := hexp.2.1
  change expansionMap[idx]? = some ((system expandedRows).run n).index at hm
  rcases hn with h1 | h6
  · have he : idx = 1 := source_marker_preimage_one ⟨idx,hsize⟩ (by simpa [h1] using hm)
    exact ⟨j,hj,Or.inl he,hsource,hproj,hexp⟩
  · have he : idx = 6 := source_marker_preimage_six ⟨idx,hsize⟩ (by simpa [h6] using hm)
    exact ⟨j,hj,Or.inr he,hsource,hproj,hexp⟩

end Shared.PNP.Record285.ExpansionBoundary

namespace Shared.PNP.Record285.ExpansionBoundary
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.GrammarCoreGraph

/-- The corresponding pre-zero-elimination graph state is also at row 1 or 6,
with every logical bank field related by the checked ownership map. -/
theorem source_boundary_is_input_marker (i : Nat) :
    let r := SourceControllerSimulation.simulation.toEventRefinement
    let n := 1+r.boundary i
    ∃ j, n = exactRefinement.boundary j ∧
      (((system logicalRows).run j).index = 1 ∨ ((system logicalRows).run j).index = 6) ∧
      SourceControllerSimulation.Rel (Source.controller.run i)
        (SourceControllerSimulation.shiftedGraph.run (r.boundary i)) ∧
      RegisterProjection.Rel RegisterProjection.lift expandedRows
        ((system RegisterProjection.originalRows).run n) ((system expandedRows).run n) ∧
      ExpansionRel logicalRows expansionMap ((system logicalRows).run j) ((system expandedRows).run n) ∧
      CoalescedRel logicalRows logicalMasks GrammarCoreZero.inputRows GrammarCoreZero.masks classMap graphMap
        ((system logicalRows).run j)
        ((coreSystem GrammarCoreZero.inputRows).run (acceptedCoalescing.boundary j)) ∧
      (((coreSystem GrammarCoreZero.inputRows).run (acceptedCoalescing.boundary j)).index = 1 ∨
       ((coreSystem GrammarCoreZero.inputRows).run (acceptedCoalescing.boundary j)).index = 6) := by
  dsimp only
  obtain ⟨j,hj,hidx,hsource,hproj,hexp⟩ := source_boundary_logical_marker i
  have hco := acceptedCoalescing.related j
  change CoalescedRel logicalRows logicalMasks GrammarCoreZero.inputRows GrammarCoreZero.masks classMap graphMap
    ((system logicalRows).run j)
    ((coreSystem GrammarCoreZero.inputRows).run (acceptedCoalescing.boundary j)) at hco
  have hmap := hco.2.1
  have hm : ((coreSystem GrammarCoreZero.inputRows).run (acceptedCoalescing.boundary j)).index = 1 ∨
      ((coreSystem GrammarCoreZero.inputRows).run (acceptedCoalescing.boundary j)).index = 6 := by
    rcases hidx with h1 | h6
    · left
      rw [h1] at hmap
      have he : graphMap[1]? = some 1 := by decide
      rw [he] at hmap
      exact Option.some.inj hmap |>.symm
    · right
      rw [h6] at hmap
      have he : graphMap[6]? = some 6 := by decide
      rw [he] at hmap
      exact Option.some.inj hmap |>.symm
  exact ⟨j,hj,hidx,hsource,hproj,hexp,hco,hm⟩

end Shared.PNP.Record285.ExpansionBoundary
