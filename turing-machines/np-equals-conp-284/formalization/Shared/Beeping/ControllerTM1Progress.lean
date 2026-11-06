import Shared.Beeping.ControllerTM2Candidates
import Shared.Beeping.ComparisonTM2

/-! Connect the looping controller to mathlib's TM2-to-TM1 translation.
The library proves positive finite segments. Event preservation additionally
requires the explicitly stated interior-label isolation property below. -/
namespace Shared.Beeping.ControllerTM1Progress
open Turing Turing.PartrecToTM2 Turing.ToPartrec
open Shared.Beeping.ControllerTM2Loop Shared.Beeping.ControllerTM2Refinement
open Shared.Beeping.ComparisonTM2 Shared.ComplexityBridge.TM2Symbols

abbrev Alphabet := TM2to1.Γ' K' (fun _ => Γ')
abbrev Labels := TM2to1.Λ' K' (fun _ => Γ') Label (Option Γ')
abbrev Conf1 := TM1.Cfg Alphabet Labels (Option Γ')

def program1 (c : Code) : Labels → TM1.Stmt Alphabet Labels (Option Γ') :=
  TM2to1.tr (program c)

def initial1 : Conf1 := TM1.init (TM2to1.trInit K'.main [])

/-- The emulator's finite initial tape is only the stack-bottom marker. -/
theorem initial_input : TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main ([] : List Γ') =
    [(true,fun _ => none)] := by rfl

noncomputable def support1 (c : Code) : Finset Labels :=
  TM2to1.trSupp (program c) (support c)

theorem support1_correct (c : Code) : TM1.Supports (program1 c) (support1 c) :=
  TM2to1.tr_supports (program c) (program_support c)

def flag1 : Labels → Bool
  | .normal q => flag q
  | _ => false

def system1 (c : Code) : EventSystem Conf1 where
  initial := initial1
  step x := ((TM1.step (program1 c) x).getD x,x.l.elim false flag1)

theorem initial_beep (c : Code) : (system1 c).BeepAt 0 := by rfl

def Rel (x : Conf) (y : Conf1) : Prop := TM2to1.TrCfg x y ∧ x.l ≠ none

theorem initial_related : Rel initial initial1 := by
  constructor
  · have h := TM2to1.trCfg_init (K := K') (Γ := fun _ => Γ') (Λ := Label)
      (σ := Option Γ') K'.main []
    have he : (TM2.init K'.main [] : Conf) = initial := by
      simp only [TM2.init,initial]
      congr 1
      funext k
      cases k <;> rfl
    rw [he] at h
    exact h
  · simp [initial]

theorem source_step (c : Code) (x : Conf) (h : x.l ≠ none) :
    ∃ y, TM2.step (program c) x = some y ∧ y.l ≠ none := by
  cases x with
  | mk l v st =>
    cases l with
    | none => simp at h
    | some q => exact ⟨TM2.stepAux (program c q) v st,rfl,program_step_live c q v st⟩

theorem reaches1_steps {α : Type} {f : α → Option α} {x y : α}
    (h : StateTransition.Reaches₁ f x y) :
    ∃ d, 0 < d ∧ runSteps f d x = some y := by
  induction h with
  | single h => exact ⟨1,by omega,by simpa [runSteps] using h⟩
  | @tail a b h hab ih =>
    obtain ⟨d,hd,hr⟩ := ih
    refine ⟨d+1,by omega,?_⟩
    change (runSteps f d _).bind f = _
    rw [hr]
    exact hab

theorem advance_run {α : Type} (f : α → Option α) (initial : α) (beep : α → Bool) (x y : α) (d : Nat)
    (h : runSteps f d x = some y) :
    (EventSystem.mk initial (fun a => ((f a).getD a,beep a))).advance x d = y := by
  induction d generalizing y with
  | zero => change some x = some y at h; cases Option.some.inj h; rfl
  | succ d ih =>
    change (runSteps f d x).bind f = some y at h
    cases hr : runSteps f d x with
    | none => simp [hr] at h
    | some mid =>
      have hm : f mid = some y := by simpa [hr] using h
      change (f ((EventSystem.mk initial (fun a => ((f a).getD a,beep a))).advance x d)).getD _ = _
      rw [ih mid hr,hm]
      rfl

/-- Mathlib supplies an actual nonempty target segment for every related
live source configuration, with a related live endpoint. -/
theorem local_progress (c : Code) (x : Conf) (y : Conf1) (h : Rel x y) :
    ∃ d z, 0 < d ∧ runSteps (TM1.step (program1 c)) d y = some z ∧
      Rel ((system c).step x).1 z := by
  obtain ⟨x',hx,hx'⟩ := source_step c x h.2
  have ht := TM2to1.tr_respects (program c) h.1
  rw [hx] at ht
  obtain ⟨z,hz,hreach⟩ := ht
  obtain ⟨d,hd,hr⟩ := reaches1_steps hreach
  refine ⟨d,z,hd,hr,?_⟩
  constructor
  · simpa [system,hx] using hz
  · simpa [system,hx] using hx'

noncomputable def duration (c : Code) (x : Conf) (y : Conf1) : Nat := by
  classical
  exact if h : Rel x y then Nat.find (local_progress c x y h) else 1

theorem duration_spec (c : Code) (x : Conf) (y : Conf1) (h : Rel x y) :
    ∃ z, 0 < duration c x y ∧
      runSteps (TM1.step (program1 c)) (duration c x y) y = some z ∧
      Rel ((system c).step x).1 z := by
  classical
  have hs := Nat.find_spec (local_progress c x y h)
  simp only [duration,dif_pos h]
  exact hs

theorem duration_positive (c : Code) (x : Conf) (y : Conf1) (h : Rel x y) :
    0 < duration c x y := by
  obtain ⟨z,hp,_,_⟩ := duration_spec c x y h
  exact hp

theorem duration_next (c : Code) (x : Conf) (y : Conf1) (h : Rel x y) :
    Rel ((system c).step x).1 ((system1 c).advance y (duration c x y)) := by
  obtain ⟨z,_,hz,hr⟩ := duration_spec c x y h
  have ha := advance_run (TM1.step (program1 c)) initial1 (fun a => a.l.elim false flag1)
    y z (duration c x y) hz
  change (system1 c).advance y (duration c x y) = z at ha
  rw [ha]
  exact hr

/-- At a related macrostep boundary, both models have the same flag. -/
theorem boundary_flag (c : Code) (x : Conf) (y : Conf1) (h : Rel x y) :
    ((system c).step x).2 = ((system1 c).step y).2 := by
  obtain ⟨hrel,_⟩ := h
  cases hrel with
  | @mk q v S L hL => cases q <;> rfl

def mute {α : Type} (S : EventSystem α) : EventSystem α :=
  ⟨S.initial,fun x => ((S.step x).1,false)⟩

theorem mute_advance {α : Type} (S : EventSystem α) (x : α) (t : Nat) :
    (mute S).advance x t = S.advance x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (S.step ((mute S).advance x t)).1 = (S.step (S.advance x t)).1
    rw [ih]

theorem mute_run {α : Type} (S : EventSystem α) (t : Nat) :
    (mute S).run t = S.run t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [EventSystem.run_succ,EventSystem.run_succ,ih]
    rfl

/-- The library translation supplies unconditional run coverage and
progress. Its observable flags are handled separately below. -/
noncomputable def progress (c : Code) : SegmentSimulation (mute (system c)) (mute (system1 c)) where
  Rel := Rel
  initial := initial_related
  duration := duration c
  positive := duration_positive c
  next := by
    intro x y h
    change Rel ((system c).step x).1 ((mute (system1 c)).advance y (duration c x y))
    rw [mute_advance]
    exact duration_next c x y h
  event_iff := by
    intro x y h
    simp [mute,EventSystem.BeepFrom]
  event_unique := by
    intro x y h j k hj hk hjb
    simp [mute,EventSystem.BeepFrom] at hjb

theorem related_boundary (c : Code) (i : Nat) :
    Rel ((system c).run i) ((system1 c).run ((progress c).boundary i)) := by
  have h := (progress c).related_boundary i
  change Rel ((mute (system c)).run i) ((mute (system1 c)).run ((progress c).boundary i)) at h
  simpa [mute_run] using h

theorem boundaries_unbounded (c : Code) (t : Nat) :
    ∃ i, t < (progress c).boundary i :=
  (progress c).toEventRefinement.boundaries_unbounded t

theorem boundary_succ (c : Code) (i : Nat) :
    (progress c).boundary (i+1) = (progress c).boundary i +
      duration c ((system c).run i) ((system1 c).run ((progress c).boundary i)) := by
  simp only [SegmentSimulation.boundary]
  change (progress c).boundary i + duration c ((mute (system c)).run i)
    ((mute (system1 c)).run ((progress c).boundary i)) = _
  rw [mute_run,mute_run]

/-- No translated execution can halt inside a segment: every target time is
covered by a finite segment whose next TM1 step is defined. -/
theorem run_never_halts (c : Code) (t : Nat) : ((system1 c).run t).l ≠ none := by
  obtain ⟨i,hlo,hhi⟩ := (progress c).toEventRefinement.covers t
  change (progress c).boundary i ≤ t at hlo
  change t < (progress c).boundary (i+1) at hhi
  let x := (system c).run i
  let y := (system1 c).run ((progress c).boundary i)
  have hr : Rel x y := related_boundary c i
  let d := duration c x y
  have hend : (progress c).boundary (i+1) = (progress c).boundary i + d := by
    simp only [SegmentSimulation.boundary]
    change (progress c).boundary i + duration c ((mute (system c)).run i)
      ((mute (system1 c)).run ((progress c).boundary i)) = _
    simp [mute_run,x,y,d]
  let j := t - (progress c).boundary i
  have hj : j < d := by omega
  obtain ⟨z,_,hz,_⟩ := duration_spec c x y hr
  have hz' : runSteps (TM1.step (program1 c)) d y = some z := hz
  obtain ⟨p,hp⟩ := ComparisonCommit.run_prefix (TM1.step (program1 c)) y z d j hz' (by omega)
  obtain ⟨next,hn⟩ := ComparisonCommit.run_prefix (TM1.step (program1 c)) y z d (j+1) hz' (by omega)
  have hs : TM1.step (program1 c) p = some next := by
    change (runSteps (TM1.step (program1 c)) j y).bind (TM1.step (program1 c)) = some next at hn
    simpa [hp] using hn
  have ha := advance_run (TM1.step (program1 c)) initial1 (fun a => a.l.elim false flag1) y p j hp
  change (system1 c).advance y j = p at ha
  have ht : (system1 c).run t = p := by
    have he : t = (progress c).boundary i + j := by dsimp [j]; omega
    rw [he,EventSystem.run_add]
    exact ha
  rw [ht]
  cases p with
  | mk l v tape =>
    cases l with
    | none => simp [TM1.step] at hs
    | some q => simp

/-- The exact missing event obligation: no TM1 microstep after the initial
boundary and before the next one visits either marked normal label. -/
def InteriorSilent (c : Code) : Prop :=
  ∀ x y, Rel x y → ∀ j, 0 < j → j < duration c x y → ¬ (system1 c).BeepFrom y j

/-- A weaker obligation only concerns the one actual run and the chosen
least matching positive segment at each boundary. -/
def RunInteriorSilent (c : Code) : Prop :=
  ∀ i j, 0 < j →
    j < duration c ((system c).run i) ((system1 c).run ((progress c).boundary i)) →
      ¬ (system1 c).BeepAt ((progress c).boundary i + j)

theorem interior_implies_run (c : Code) (h : InteriorSilent c) : RunInteriorSilent c := by
  intro i j hj hd
  have hh := h _ _ (related_boundary c i) j hj hd
  rwa [← EventSystem.beepAt_add_iff] at hh

theorem boundary_beep_iff (c : Code) (i : Nat) :
    (system c).BeepAt i ↔ (system1 c).BeepAt ((progress c).boundary i) := by
  unfold EventSystem.BeepAt
  rw [boundary_flag c _ _ (related_boundary c i)]

/-- The weaker run-local obligation suffices for full event refinement. -/
noncomputable def runRefinement (c : Code) (hquiet : RunInteriorSilent c) :
    EventRefinement (system c) (system1 c) where
  Rel := Rel
  boundary := (progress c).boundary
  boundary_zero := (progress c).toEventRefinement.boundary_zero
  progress := (progress c).toEventRefinement.progress
  related := related_boundary c
  event_iff := by
    intro i
    constructor
    · intro hb
      refine ⟨(progress c).boundary i,le_rfl,?_,(boundary_beep_iff c i).1 hb⟩
      exact (progress c).toEventRefinement.progress i
    · rintro ⟨j,hlo,hhi,hb⟩
      have hj : j = (progress c).boundary i := by
        by_contra hn
        have hp : 0 < j - (progress c).boundary i := by omega
        have hd : j - (progress c).boundary i < duration c ((system c).run i)
            ((system1 c).run ((progress c).boundary i)) := by
          have he := boundary_succ c i
          omega
        have hq := hquiet i (j - (progress c).boundary i) hp hd
        have he : (progress c).boundary i + (j - (progress c).boundary i) = j := by omega
        rw [he] at hq
        exact hq hb
      subst j
      exact (boundary_beep_iff c i).2 hb
  event_unique := by
    intro i j k hj hj' hk hk' hjb hkb
    have hs (t : Nat) (hlo : (progress c).boundary i ≤ t)
        (hhi : t < (progress c).boundary (i+1)) (hb : (system1 c).BeepAt t) :
        t = (progress c).boundary i := by
      by_contra hn
      have hp : 0 < t - (progress c).boundary i := by omega
      have hd : t - (progress c).boundary i < duration c ((system c).run i)
          ((system1 c).run ((progress c).boundary i)) := by
        have he := boundary_succ c i
        omega
      have hq := hquiet i (t - (progress c).boundary i) hp hd
      have he : (progress c).boundary i + (t - (progress c).boundary i) = t := by omega
      rw [he] at hq
      exact hq hb
    rw [hs j hj hj' hjb,hs k hk hk' hkb]

/-- If the concrete translator has no interior marked labels, its already
proved positive segments give a full event-preserving refinement. -/
noncomputable def simulation (c : Code) (hquiet : InteriorSilent c) :
    SegmentSimulation (system c) (system1 c) where
  Rel := Rel
  initial := initial_related
  duration := duration c
  positive := duration_positive c
  next := duration_next c
  event_iff := by
    intro x y h
    have hf := boundary_flag c x y h
    constructor
    · intro hb
      refine ⟨0,duration_positive c x y h,?_⟩
      change ((system1 c).step y).2 = true
      rw [← hf]
      exact hb
    · rintro ⟨j,hj,hb⟩
      have he : j = 0 := by
        by_contra hn
        exact hquiet x y h j (by omega) hj hb
      subst j
      change ((system1 c).step y).2 = true at hb
      rw [← hf] at hb
      exact hb
  event_unique := by
    intro x y h j k hj hk hjb hkb
    have hj0 : j = 0 := by
      by_contra hn
      exact hquiet x y h j (by omega) hj hjb
    have hk0 : k = 0 := by
      by_contra hn
      exact hquiet x y h k (by omega) hk hkb
    omega

theorem pnp_conditional (c : Code)
    (hc : CodeCorrect Shared.PNP.TM2Candidate.compareSAT c) (hquiet : RunInteriorSilent c) :
    (system1 c).EventuallySilent ↔
      ∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
        Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
          some (Shared.ComplexityBridge.CNF.sat x) := by
  exact (runRefinement c hquiet).eventuallySilent_iff.symm.trans
    (((ControllerTM2Refinement.simulation Shared.PNP.TM2Candidate.compareSAT c hc).toEventRefinement.eventuallySilent_iff).symm.trans
      Shared.PNP.TM2Candidate.controller_silent_iff)

theorem npconp_conditional (c : Code)
    (hc : CodeCorrect Shared.NPCONP.TM2Verifier.compare c) (hquiet : RunInteriorSilent c) :
    (system1 c).EventuallySilent ↔
      ∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
        Shared.NPCONP.TM2Verifier.test verifier x = true := by
  exact (runRefinement c hquiet).eventuallySilent_iff.symm.trans
    (((ControllerTM2Refinement.simulation Shared.NPCONP.TM2Verifier.compare c hc).toEventRefinement.eventuallySilent_iff).symm.trans
      Shared.NPCONP.TM2Verifier.controller_silent_iff)

end Shared.Beeping.ControllerTM1Progress
