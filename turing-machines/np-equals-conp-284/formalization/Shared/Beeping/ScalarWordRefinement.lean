import Shared.Beeping.WordBridge

/-! A scalar event simulation yields an ordered unit-word simulation with
exactly the same positive segment durations. This construction is specific to
unit events; it cannot recover bit values erased from a richer output stream. -/
namespace PASoundness.ScalarWordRefinement
open Shared.Beeping

@[simp] theorem advance_ofBeep {C : Type} (M : EventSystem C) (c : C) (k : Nat) :
    (WordEventSystem.ofBeep M).advance c k = M.advance c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (M.step ((WordEventSystem.ofBeep M).advance c k)).1 = (M.step (M.advance c k)).1
    rw [ih]

/-- A target segment with no flagged transitions emits the empty unit word. -/
theorem wordFrom_silent {C : Type} (M : EventSystem C) (c : C) (k : Nat)
    (h : ∀ j, j < k → ¬ M.BeepFrom c j) :
    (WordEventSystem.ofBeep M).wordFrom c k = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : ∀ j, j < k → ¬ M.BeepFrom c j := fun j hj => h j (by omega)
    have hn := h k (by omega)
    have hf : (M.step (M.advance c k)).2 = false := by
      cases he : (M.step (M.advance c k)).2 with
      | false => rfl
      | true => exact False.elim (hn he)
    change (WordEventSystem.ofBeep M).wordFrom c k ++
      (if (M.step ((WordEventSystem.ofBeep M).advance c k)).2 then [()] else []) = []
    rw [advance_ofBeep,ih hp,hf]
    rfl

/-- A segment containing exactly one flagged transition emits exactly one
unit event, regardless of where within the segment the event occurs. -/
theorem wordFrom_unique {C : Type} (M : EventSystem C) (c : C) (k j : Nat)
    (hj : j < k) (hb : M.BeepFrom c j)
    (hu : ∀ i, i < k → M.BeepFrom c i → i = j) :
    (WordEventSystem.ofBeep M).wordFrom c k = [()] := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : j = k
    · subst j
      have hs : ∀ i, i < k → ¬ M.BeepFrom c i := by
        intro i hi hb'
        have := hu i (by omega) hb'
        omega
      have hf : (M.step (M.advance c k)).2 = true := hb
      change (WordEventSystem.ofBeep M).wordFrom c k ++
        (if (M.step ((WordEventSystem.ofBeep M).advance c k)).2 then [()] else []) = [()]
      rw [advance_ofBeep,wordFrom_silent M c k hs,hf]
      rfl
    · have hj' : j < k := by omega
      have hu' : ∀ i, i < k → M.BeepFrom c i → i = j :=
        fun i hi hbi => hu i (by omega) hbi
      have hn : ¬ M.BeepFrom c k := by
        intro hbk
        exact he (hu k (by omega) hbk).symm
      have hf : (M.step (M.advance c k)).2 = false := by
        cases hh : (M.step (M.advance c k)).2 with
        | false => rfl
        | true => exact False.elim (hn hh)
      change (WordEventSystem.ofBeep M).wordFrom c k ++
        (if (M.step ((WordEventSystem.ofBeep M).advance c k)).2 then [()] else []) = [()]
      rw [advance_ofBeep,ih hj' hu',hf]
      rfl

/-- Every scalar local simulation supplies the stronger exact unit-word
segment contract used by the shared ordered-output library. -/
def toWordSimulation {S T : Type} {source : EventSystem S} {target : EventSystem T}
    (r : Shared.Beeping.SegmentSimulation source target) :
    PASoundness.SegmentSimulation (WordEventSystem.ofBeep source) (WordEventSystem.ofBeep target) where
  Rel := r.Rel
  startup := 0
  initial := r.initial
  startup_silent := rfl
  duration := r.duration
  positive := r.positive
  next := by
    intro s t h
    change r.Rel (source.step s).1 ((WordEventSystem.ofBeep target).advance t (r.duration s t))
    rw [advance_ofBeep]
    exact r.next s t h
  word_eq := by
    intro s t h
    cases hb : (source.step s).2 with
    | false =>
      have hs : ∀ j, j < r.duration s t → ¬ target.BeepFrom t j := by
        intro j hj he
        have bad := (r.event_iff s t h).2 ⟨j,hj,he⟩
        simp [hb] at bad
      simpa [WordEventSystem.ofBeep,hb] using wordFrom_silent target t (r.duration s t) hs
    | true =>
      obtain ⟨j,hj,he⟩ := (r.event_iff s t h).1 hb
      have hu : ∀ i, i < r.duration s t → target.BeepFrom t i → i = j := by
        intro i hi hbi
        exact r.event_unique s t h i j hi hj hbi he
      simpa [WordEventSystem.ofBeep,hb] using wordFrom_unique target t (r.duration s t) j hj he hu

/-- Consequently every scalar positive-block simulation preserves the entire
ordered sequence of unit beeps, not merely eventual silence. -/
theorem sameOutput {S T : Type} {source : EventSystem S} {target : EventSystem T}
    (r : Shared.Beeping.SegmentSimulation source target) :
    SameOutput (WordEventSystem.ofBeep source) (WordEventSystem.ofBeep target) :=
  (toWordSimulation r).sameOutput

/-- The same exact event sequence, relabeled as Boolean `true` bits. -/
def beepBits {C : Type} (M : EventSystem C) : WordEventSystem C Bool :=
  (WordEventSystem.ofBeep M).map (fun _ => true)

theorem sameBitOutput {S T : Type} {source : EventSystem S} {target : EventSystem T}
    (r : Shared.Beeping.SegmentSimulation source target) :
    SameOutput (beepBits source) (beepBits target) :=
  ((toWordSimulation r).toRefinement.map (fun _ => true)).sameOutput

/-- The finite-table word view used by the hierarchy has precisely the
singleton `true` output obtained by relabeling scalar beep events. -/
theorem beepBits_machine {n : Nat} (M : Shared.Beeping.Machines.Machine n) :
    beepBits M.system = machineWordSystem M (BitLabels.fromFlags M) := by
  have extWord : ∀ {C A : Type} {W V : WordEventSystem C A},
      W.initial = V.initial → W.step = V.step → W = V := by
    intro C A W V hi hs
    cases W
    cases V
    simp_all
  apply extWord
  · rfl
  · funext c
    simp only [beepBits,WordEventSystem.map,WordEventSystem.ofBeep,machineWordSystem,
      BitLabels.fromFlags,BitLabels.at_ofFn,Shared.Beeping.Machines.Machine.system,
      Shared.Beeping.Machines.Machine.step]
    have hb (b : Bool) : (if b then [()] else []).map (fun _ => true) =
        (if b then some true else none).toList := by cases b <;> rfl
    congr 1
    exact hb (M.table.row c.state (c.tape c.head)).beep

end PASoundness.ScalarWordRefinement
