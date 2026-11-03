import Shared.PNP.Record285.ExpansionBoundary

/-! Give the checked zero-elimination pass an exact deterministic duration. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.ZeroBoundary
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero

theorem rewrite_local_progress_exact (before after : Array CoreRow) (masks : Array (Array Nat))
    (selected : List Nat) (mapping : Array Nat)
    (hcheck : check before masks = true) (hall : selected.all (selectedZero before masks) = true)
    (hrewrite : rewriteCheck before after selected mapping = true)
    (post pre : CoreState) (hrel : RewriteRel before after masks mapping post pre) :
    let k := if selected.contains ((coreStep before pre).1.index) then 1 else 0
    k ≤ 1 ∧ RewriteRel before after masks mapping (coreStep after post).1
        ((coreSystem before).advance pre (k+1)) ∧
      (coreStep after post).2 = (coreStep before pre).2 ∧
      ∀ j, j < k → ¬ (coreSystem before).BeepFrom pre (j+1) := by
  dsimp only
  obtain ⟨hpostidx,hmap,hfields,hvalid⟩ := hrel
  obtain ⟨postrow,hpost⟩ : ∃ row, after[post.index]? = some row :=
    ⟨after[post.index],by simp⟩
  have hc := rewriteCheck_at before after selected mapping hrewrite post.index hpostidx
  obtain ⟨prerow,no,yes,hpre,_,hedge,hno,hyes,hshortno,hshortyes⟩ :=
    rewriteRow_sound before after selected mapping post.index pre.index postrow hmap hpost hc
  let branch := GrammarControlGraph.test postrow.edge post.fields
  let postNext := if branch then postrow.yes else postrow.no
  let preNext := if branch then prerow.yes else prerow.no
  let mapped := if branch then yes else no
  have hnextmap : mapping[postNext]? = some mapped := by
    dsimp [postNext,mapped]
    cases branch <;> simp_all
  have hshort : shortcut before selected preNext = some mapped := by
    dsimp [preNext,mapped]
    cases branch <;> simp_all
  have hpostNext : postNext < after.size := by
    obtain ⟨hm,_⟩ := Array.getElem?_eq_some_iff.mp hnextmap
    have hz := (rewrite_sizes before after selected mapping hrewrite).1
    omega
  have hprestep : coreStep before pre =
      (⟨preNext,applyUpdate postrow.edge pre.fields⟩,decide (postrow.edge = .beep)) := by
    simp [coreStep,hpre,hedge,preNext,branch,hfields]
  have hpoststep : coreStep after post =
      (⟨postNext,applyUpdate postrow.edge post.fields⟩,decide (postrow.edge = .beep)) := by
    simp [coreStep,hpost,postNext,branch]
  let mid : CoreState := ⟨preNext,applyUpdate postrow.edge pre.fields⟩
  have hmidValid : Valid before masks mid := by
    have hv := step_preserves before masks hcheck pre hvalid
    rw [hprestep] at hv
    exact hv
  have hevent : (coreStep after post).2 = (coreStep before pre).2 := by rw [hprestep,hpoststep]
  cases hsel : selected.contains preNext with
  | false =>
    cases hr : before[preNext]? with
    | none => simp [shortcut,hr] at hshort
    | some row =>
      have hnmem : preNext ∉ selected := by simpa using hsel
      have hidentity : mapped = preNext := by simpa [shortcut,hr,hnmem] using hshort.symm
      have hnextmap' : mapping[postNext]? = some preNext := by simpa [hidentity] using hnextmap
      have hk : (if selected.contains ((coreStep before pre).1.index) then 1 else 0) = 0 := by
        rw [hprestep]
        simp [hnmem]
      rw [hk]
      refine ⟨by omega,?_,hevent,by simp⟩
      rw [hpoststep]
      change RewriteRel before after masks mapping ⟨postNext,applyUpdate postrow.edge post.fields⟩
        ((coreSystem before).advance pre 1)
      change RewriteRel before after masks mapping ⟨postNext,applyUpdate postrow.edge post.fields⟩
        (coreStep before pre).1
      rw [hprestep]
      change postNext < after.size ∧ mapping[postNext]? = some preNext ∧
        applyUpdate postrow.edge post.fields = applyUpdate postrow.edge pre.fields ∧ Valid before masks mid
      exact ⟨hpostNext,hnextmap',by simp [hfields],hmidValid⟩
  | true =>
    have hmem : mid.index ∈ selected := by simpa [mid] using hsel
    obtain ⟨next,hskip,hshortcut⟩ := selected_step before masks selected hall mid hmidValid hmem
    have hidentity : mapped = next := by
      have hh : shortcut before selected preNext = some next := by simpa [mid] using hshortcut
      rw [hh] at hshort
      exact Option.some.inj hshort |>.symm
    have hnextmap' : mapping[postNext]? = some next := by simpa [hidentity] using hnextmap
    have hk : (if selected.contains ((coreStep before pre).1.index) then 1 else 0) = 1 := by
      rw [hprestep]
      have hm : preNext ∈ selected := by simpa [mid] using hmem
      simp [hm]
    rw [hk]
    refine ⟨by omega,?_,hevent,?_⟩
    · rw [hpoststep]
      change RewriteRel before after masks mapping ⟨postNext,applyUpdate postrow.edge post.fields⟩
        ((coreSystem before).advance pre 2)
      change RewriteRel before after masks mapping ⟨postNext,applyUpdate postrow.edge post.fields⟩
        (coreStep before (coreStep before pre).1).1
      rw [hprestep]
      change RewriteRel before after masks mapping ⟨postNext,applyUpdate postrow.edge post.fields⟩
        (coreStep before mid).1
      rw [hskip]
      change postNext < after.size ∧ mapping[postNext]? = some next ∧
        applyUpdate postrow.edge post.fields = mid.fields ∧ Valid before masks ⟨next,mid.fields⟩
      exact ⟨hpostNext,hnextmap',by simp [mid,hfields],by
        have hv := step_preserves before masks hcheck mid hmidValid
        rw [hskip] at hv
        exact hv⟩
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      change ¬ (coreStep before (coreStep before pre).1).2 = true
      rw [hprestep]
      change ¬ (coreStep before mid).2 = true
      rw [hskip]
      simp


end Shared.PNP.Record285.ZeroBoundary

namespace Shared.PNP.Record285.ZeroBoundary
open Shared.Beeping
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero

def exactDuration (pre : CoreState) : Nat :=
  (if zeroRows.contains ((coreStep inputRows pre).1.index) then 1 else 0)+1

/-- The checked zero-elimination pass takes exactly one input step, plus one
when that step reaches one of the five certified zero rows. -/
noncomputable def exactSimulation : SegmentSimulation (coreSystem producerRows) (coreSystem inputRows) where
  Rel := RewriteRel inputRows producerRows masks retainedMap
  initial := rewrite_initial inputRows producerRows masks zeroRows retainedMap
    input_invariant_checked rewrite_checked (by decide) (by decide)
  duration := fun _ pre => exactDuration pre
  positive := by
    intro post pre h
    simp only [exactDuration]
    omega
  next := by
    intro post pre h
    have hp := rewrite_local_progress_exact inputRows producerRows masks zeroRows retainedMap
      input_invariant_checked selected_zero_checked rewrite_checked post pre h
    exact hp.2.1
  event_iff := by
    intro post pre h
    have hp := rewrite_local_progress_exact inputRows producerRows masks zeroRows retainedMap
      input_invariant_checked selected_zero_checked rewrite_checked post pre h
    constructor
    · intro he
      refine ⟨0,by simp [exactDuration],?_⟩
      change (coreStep inputRows pre).2 = true
      change (coreStep producerRows post).2 = true at he
      exact hp.2.2.1.symm.trans he
    · rintro ⟨j,hj,he⟩
      have hz := quiet_only_first_core inputRows pre _ j hp.2.2.2 hj he
      subst j
      change (coreStep inputRows pre).2 = true at he
      change (coreStep producerRows post).2 = true
      exact hp.2.2.1.trans he
  event_unique := by
    intro post pre h j k hj hk hjbeep hkbeep
    have hp := rewrite_local_progress_exact inputRows producerRows masks zeroRows retainedMap
      input_invariant_checked selected_zero_checked rewrite_checked post pre h
    have hj0 := quiet_only_first_core inputRows pre _ j hp.2.2.2 hj hjbeep
    have hk0 := quiet_only_first_core inputRows pre _ k hp.2.2.2 hk hkbeep
    omega

noncomputable def exactRefinement : EventRefinement (coreSystem producerRows) (coreSystem inputRows) :=
  exactSimulation.toEventRefinement

theorem marker_not_selected (pc : Nat) (h : pc = 1 ∨ pc = 6) : pc ∉ zeroRows := by
  rcases h with rfl | rfl <;> decide

/-- A pre-elimination graph state at row 1 or 6 cannot be the eliminated
intermediate zero test, hence it is a retained producer-core boundary. -/
theorem marker_is_exact_boundary (n : Nat)
    (hmarker : ((coreSystem inputRows).run n).index = 1 ∨
      ((coreSystem inputRows).run n).index = 6) :
    ∃ i, n = exactRefinement.boundary i := by
  let r := exactRefinement
  obtain ⟨i,hlo,hhi⟩ := r.covers n
  let pre := (coreSystem inputRows).run (r.boundary i)
  let k := n-r.boundary i
  have hn : n = r.boundary i+k := by dsimp [k]; omega
  have hbound : r.boundary (i+1) = r.boundary i+exactDuration pre := by rfl
  have hk : k < exactDuration pre := by rw [hbound] at hhi; omega
  by_cases hsel : zeroRows.contains ((coreStep inputRows pre).1.index)
  · have hmem : (coreStep inputRows pre).1.index ∈ zeroRows := by simpa using hsel
    have hd : exactDuration pre = 2 := by simp [exactDuration,hmem]
    have hk' : k < 2 := by simpa [hd] using hk
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with hk0 | hk1
    · exact ⟨i,by simpa [hk0] using hn⟩
    · have hmark : ((coreStep inputRows pre).1.index = 1 ∨
          (coreStep inputRows pre).1.index = 6) := by
        rw [hn,EventSystem.run_add] at hmarker
        simpa [pre,hk1,EventSystem.advance,coreSystem] using hmarker
      exact False.elim (marker_not_selected _ hmark hmem)
  · have hmem : (coreStep inputRows pre).1.index ∉ zeroRows := by simpa using hsel
    have hd : exactDuration pre = 1 := by simp [exactDuration,hmem]
    have hk' : k < 1 := by simpa [hd] using hk
    have hk0 : k = 0 := by omega
    exact ⟨i,by simpa [hk0] using hn⟩

end Shared.PNP.Record285.ZeroBoundary

namespace Shared.PNP.Record285.ZeroBoundary
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero

/-- Every source-controller action boundary aligns with both a logical graph
boundary and a retained producer-core boundary. The entire register-bank
relations across projection, expansion, ownership and zero elimination are
retained in the witness. -/
theorem source_boundary_is_producer_boundary (i : Nat) :
    let r := SourceControllerSimulation.simulation.toEventRefinement
    let n := 1+r.boundary i
    ∃ j m,
      n = ExpansionBoundary.exactRefinement.boundary j ∧
      acceptedCoalescing.boundary j = exactRefinement.boundary m ∧
      SourceControllerSimulation.Rel (Source.controller.run i)
        (SourceControllerSimulation.shiftedGraph.run (r.boundary i)) ∧
      RegisterProjection.Rel RegisterProjection.lift expandedRows
        ((system RegisterProjection.originalRows).run n) ((system expandedRows).run n) ∧
      ExpansionRel logicalRows expansionMap ((system logicalRows).run j) ((system expandedRows).run n) ∧
      CoalescedRel logicalRows logicalMasks inputRows masks classMap graphMap
        ((system logicalRows).run j) ((coreSystem inputRows).run (acceptedCoalescing.boundary j)) ∧
      RewriteRel inputRows producerRows masks retainedMap ((coreSystem producerRows).run m)
        ((coreSystem inputRows).run (acceptedCoalescing.boundary j)) := by
  dsimp only
  obtain ⟨j,hj,hidx,hsource,hproj,hexp,hco,hmarker⟩ :=
    ExpansionBoundary.source_boundary_is_input_marker i
  obtain ⟨m,hm⟩ := marker_is_exact_boundary (acceptedCoalescing.boundary j) hmarker
  have hrewrite := exactRefinement.related m
  change RewriteRel inputRows producerRows masks retainedMap ((coreSystem producerRows).run m)
    ((coreSystem inputRows).run (exactRefinement.boundary m)) at hrewrite
  rw [←hm] at hrewrite
  exact ⟨j,m,hj,hm,hsource,hproj,hexp,hco,hrewrite⟩

end Shared.PNP.Record285.ZeroBoundary
