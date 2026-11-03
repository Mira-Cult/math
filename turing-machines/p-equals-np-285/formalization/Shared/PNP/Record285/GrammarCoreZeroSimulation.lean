import Shared.PNP.Record285.GrammarCoreZeroRewrite

/-! Progress-sensitive simulation for checked zero-test elimination. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarCoreGraph

def RewriteRel (before after : Array CoreRow) (masks : Array (Array Nat)) (mapping : Array Nat)
    (post pre : CoreState) : Prop :=
  post.index < after.size ∧ mapping[post.index]? = some pre.index ∧
    post.fields = pre.fields ∧ Valid before masks pre

theorem rewrite_sizes (before after : Array CoreRow) (selected : List Nat) (mapping : Array Nat)
    (h : rewriteCheck before after selected mapping = true) :
    after.size = mapping.size ∧ mapping[0]? = some 0 := by
  simp only [rewriteCheck,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  exact h.1

theorem rewrite_initial (before after : Array CoreRow) (masks : Array (Array Nat))
    (selected : List Nat) (mapping : Array Nat)
    (hcheck : check before masks = true) (hrewrite : rewriteCheck before after selected mapping = true)
    (hbefore : 0 < before.size) (hafter : 0 < after.size) :
    RewriteRel before after masks mapping (coreSystem after).initial (coreSystem before).initial := by
  refine ⟨hafter,?_,rfl,initial_valid before masks hcheck hbefore⟩
  exact (rewrite_sizes before after selected mapping hrewrite).2

/-- Each retained action takes one input transition, followed by at most one
certified silent zero decrement. -/
theorem rewrite_local_progress (before after : Array CoreRow) (masks : Array (Array Nat))
    (selected : List Nat) (mapping : Array Nat)
    (hcheck : check before masks = true) (hall : selected.all (selectedZero before masks) = true)
    (hrewrite : rewriteCheck before after selected mapping = true)
    (post pre : CoreState) (hrel : RewriteRel before after masks mapping post pre) :
    ∃ k, k ≤ 1 ∧ RewriteRel before after masks mapping (coreStep after post).1
        ((coreSystem before).advance pre (k+1)) ∧
      (coreStep after post).2 = (coreStep before pre).2 ∧
      ∀ j, j < k → ¬ (coreSystem before).BeepFrom pre (j+1) := by
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
      refine ⟨0,by omega,?_,hevent,by simp⟩
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
    refine ⟨1,by omega,?_,hevent,?_⟩
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

theorem quiet_only_first_core (before : Array CoreRow) (pre : CoreState) (k j : Nat)
    (hq : ∀ n, n < k → ¬ (coreSystem before).BeepFrom pre (n+1))
    (hj : j < k+1) (he : (coreSystem before).BeepFrom pre j) : j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    exfalso
    apply hq j (by omega)
    simpa using he

noncomputable def rewriteDuration (before after : Array CoreRow) (masks : Array (Array Nat))
    (selected : List Nat) (mapping : Array Nat)
    (hcheck : check before masks = true) (hall : selected.all (selectedZero before masks) = true)
    (hrewrite : rewriteCheck before after selected mapping = true) (post pre : CoreState) : Nat := by
  classical
  exact if h : RewriteRel before after masks mapping post pre then
    Classical.choose (rewrite_local_progress before after masks selected mapping hcheck hall hrewrite post pre h) + 1
  else 1

/-- The finite rewrite certificate and its all-natural zero invariant yield a
cofinal, event-exact refinement with durations one or two. -/
noncomputable def rewriteSimulation (before after : Array CoreRow) (masks : Array (Array Nat))
    (selected : List Nat) (mapping : Array Nat)
    (hcheck : check before masks = true) (hall : selected.all (selectedZero before masks) = true)
    (hrewrite : rewriteCheck before after selected mapping = true)
    (hbefore : 0 < before.size) (hafter : 0 < after.size) :
    SegmentSimulation (coreSystem after) (coreSystem before) where
  Rel := RewriteRel before after masks mapping
  initial := rewrite_initial before after masks selected mapping hcheck hrewrite hbefore hafter
  duration := rewriteDuration before after masks selected mapping hcheck hall hrewrite
  positive := by
    intro post pre h
    simp only [rewriteDuration,dif_pos h]
    omega
  next := by
    intro post pre h
    have hp := Classical.choose_spec
      (rewrite_local_progress before after masks selected mapping hcheck hall hrewrite post pre h)
    simp only [rewriteDuration,dif_pos h]
    exact hp.2.1
  event_iff := by
    intro post pre h
    have hp := Classical.choose_spec
      (rewrite_local_progress before after masks selected mapping hcheck hall hrewrite post pre h)
    simp only [rewriteDuration,dif_pos h]
    constructor
    · intro he
      refine ⟨0,by omega,?_⟩
      change (coreStep before pre).2 = true
      change (coreStep after post).2 = true at he
      exact hp.2.2.1.symm.trans he
    · rintro ⟨j,hj,he⟩
      have hz := quiet_only_first_core before pre _ j hp.2.2.2 hj he
      subst j
      change (coreStep before pre).2 = true at he
      change (coreStep after post).2 = true
      exact hp.2.2.1.trans he
  event_unique := by
    intro post pre h j k hj hk hjbeep hkbeep
    have hp := Classical.choose_spec
      (rewrite_local_progress before after masks selected mapping hcheck hall hrewrite post pre h)
    simp only [rewriteDuration,dif_pos h] at hj hk
    have hj0 := quiet_only_first_core before pre _ j hp.2.2.2 hj hjbeep
    have hk0 := quiet_only_first_core before pre _ k hp.2.2.2 hk hkbeep
    omega

noncomputable def rewriteRefinement (before after : Array CoreRow) (masks : Array (Array Nat))
    (selected : List Nat) (mapping : Array Nat)
    (hcheck : check before masks = true) (hall : selected.all (selectedZero before masks) = true)
    (hrewrite : rewriteCheck before after selected mapping = true)
    (hbefore : 0 < before.size) (hafter : 0 < after.size) :
    EventRefinement (coreSystem after) (coreSystem before) :=
  (rewriteSimulation before after masks selected mapping hcheck hall hrewrite hbefore hafter).toEventRefinement

end Shared.PNP.Record285.GrammarCoreZero
