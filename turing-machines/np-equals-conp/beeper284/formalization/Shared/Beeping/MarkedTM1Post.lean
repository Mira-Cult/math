import Shared.Beeping.ControllerTM1Interior
import Shared.Beeping.PostTableBinding
import Shared.Beeping.BinaryReadWrite

/-! A post-Turing interpreter for TM1 statement blocks that retains a
separate entry state. Only entry rows may beep. This module does not yet
extract a finite source table or compile it to binary. -/
namespace Shared.Beeping.MarkedTM1Post
open Turing Turing.PartrecToTM2 Turing.ToPartrec
open Shared.Beeping.ControllerTM1Progress Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.PostTableBinding

abbrev A := ControllerTM1Progress.Alphabet
abbrev L := ControllerTM1Progress.Labels
abbrev V := Option Γ'
abbrev S := TM1.Stmt A L V

inductive Phase
  | entry : L → V → Phase
  | inside : S → V → Phase
  | stopped : V → Phase

instance : Inhabited Phase := ⟨.entry default none⟩

/-- Execute one post-Turing action, preserving the next TM1 block entry
explicitly instead of identifying it with its function-valued statement. -/
def execute : S → A → V → Phase × TM0.Stmt A
  | .move dir s, a, v => (.inside s v,.move dir)
  | .write f s, a, v => (.inside s v,.write (f a v))
  | .load f s, a, v => execute s a (f a v)
  | .branch f s t, a, v => if f a v then execute s a v else execute t a v
  | .goto f, a, v => (.entry (f a v) v,.write a)
  | .halt, a, v => (.stopped v,.write a)

def table (M : L → S) : TM0.Machine A Phase
  | .entry q v, a => some (execute (M q) a v)
  | .inside s v, a => some (execute s a v)
  | .stopped v, a => some (.stopped v,.write a)

def flags (b : L → Bool) : Phase → A → Bool
  | .entry q _, _ => b q
  | _, _ => false

def encode (x : TM1.Cfg A L V) : ExternalConfig (Λ := Phase) :=
  ⟨match x.l with | some q => .entry q x.var | none => .stopped x.var,x.Tape⟩

def inner (s : S) (v : V) (T : Tape A) : ExternalConfig (Λ := Phase) := ⟨.inside s v,T⟩

def post (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V) :=
  externalSystem (table M) (flags b) (encode start)

def source (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V) : EventSystem (TM1.Cfg A L V) :=
  ⟨start,fun x => ((TM1.step M x).getD x,x.l.elim false b)⟩

theorem inner_silent (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V)
    (s : S) (v : V) (T : Tape A) :
    ((post M b start).step (inner s v T)).2 = false := by
  cases h : execute s T.head v with
  | mk q op => cases op <;> simp [post,externalSystem,externalStep,table,flags,inner,h]

theorem inner_move (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V)
    (dir : Dir) (s : S) (v : V) (T : Tape A) :
    ((post M b start).step (inner (.move dir s) v T)).1 = inner s v (T.move dir) := by
  rfl

theorem inner_write (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V)
    (f : A → V → A) (s : S) (v : V) (T : Tape A) :
    ((post M b start).step (inner (.write f s) v T)).1 = inner s v (T.write (f T.head v)) := by
  rfl

theorem inner_load_step (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V)
    (f : A → V → V) (s : S) (v : V) (T : Tape A) :
    (post M b start).step (inner (.load f s) v T) =
      (post M b start).step (inner s (f T.head v) T) := by rfl

theorem inner_branch_step (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V)
    (f : A → V → Bool) (s t : S) (v : V) (T : Tape A) :
    (post M b start).step (inner (.branch f s t) v T) =
      (post M b start).step (inner (if f T.head v then s else t) v T) := by
  cases h : f T.head v <;> simp [post,externalSystem,externalStep,table,execute,inner,flags,h]

theorem same_advance {α : Type} (F : EventSystem α) (x y : α) (h : F.step x = F.step y)
    (d : Nat) (hd : 0 < d) : F.advance x d = F.advance y d := by
  cases d with
  | zero => omega
  | succ d =>
    induction d with
    | zero => change (F.step x).1 = (F.step y).1; rw [h]
    | succ d ih =>
      change (F.step (F.advance x (d+1))).1 = (F.step (F.advance y (d+1))).1
      rw [ih (by omega)]

theorem same_beep {α : Type} (F : EventSystem α) (x y : α) (h : F.step x = F.step y)
    (j : Nat) : F.BeepFrom x j ↔ F.BeepFrom y j := by
  cases j with
  | zero => simp [EventSystem.BeepFrom,EventSystem.advance,h]
  | succ j =>
    unfold EventSystem.BeepFrom
    rw [same_advance F x y h (j+1) (by omega)]

theorem same_advance_fst {α : Type} (F : EventSystem α) (x y : α)
    (h : (F.step x).1 = (F.step y).1) (d : Nat) (hd : 0 < d) :
    F.advance x d = F.advance y d := by
  cases d with
  | zero => omega
  | succ d =>
    induction d with
    | zero => exact h
    | succ d ih =>
      change (F.step (F.advance x (d+1))).1 = (F.step (F.advance y (d+1))).1
      rw [ih (by omega)]

/-- A finite TM1 statement block always finishes in a positive number of
post-Turing transitions; all transitions in the internal phase are silent. -/
theorem inner_finishes (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V)
    (s : S) (v : V) (T : Tape A) :
    ∃ d, 0 < d ∧
      (post M b start).advance (inner s v T) d = encode (TM1.stepAux s v T) ∧
      (∀ j, j < d → ¬ (post M b start).BeepFrom (inner s v T) j) := by
  induction s generalizing v T with
  | move dir s ih =>
    obtain ⟨d,hd,hfinal,hsilent⟩ := ih v (T.move dir)
    refine ⟨1+d,by omega,?_,?_⟩
    · rw [BinaryReadWrite.advance_add]
      change (post M b start).advance (((post M b start).step (inner (.move dir s) v T)).1) d = _
      rw [inner_move]
      exact hfinal
    · intro j hj
      cases j with
      | zero => simpa [EventSystem.BeepFrom,EventSystem.advance,inner_silent]
      | succ j =>
        have he : j+1 = 1+j := by omega
        unfold EventSystem.BeepFrom
        rw [he,BinaryReadWrite.advance_add]
        change ((post M b start).step ((post M b start).advance
          (((post M b start).step (inner (.move dir s) v T)).1) j)).2 ≠ true
        rw [inner_move]
        exact hsilent j (by omega)
  | write f s ih =>
    obtain ⟨d,hd,hfinal,hsilent⟩ := ih v (T.write (f T.head v))
    refine ⟨1+d,by omega,?_,?_⟩
    · rw [BinaryReadWrite.advance_add]
      change (post M b start).advance (((post M b start).step (inner (.write f s) v T)).1) d = _
      rw [inner_write]
      exact hfinal
    · intro j hj
      cases j with
      | zero => simpa [EventSystem.BeepFrom,EventSystem.advance,inner_silent]
      | succ j =>
        have he : j+1 = 1+j := by omega
        unfold EventSystem.BeepFrom
        rw [he,BinaryReadWrite.advance_add]
        change ((post M b start).step ((post M b start).advance
          (((post M b start).step (inner (.write f s) v T)).1) j)).2 ≠ true
        rw [inner_write]
        exact hsilent j (by omega)
  | load f s ih =>
    obtain ⟨d,hd,hfinal,hsilent⟩ := ih (f T.head v) T
    have he := inner_load_step M b start f s v T
    refine ⟨d,hd,?_,?_⟩
    · rw [same_advance _ _ _ he d hd]
      exact hfinal
    · intro j hj
      rw [same_beep _ _ _ he]
      exact hsilent j hj
  | branch f s t ihs iht =>
    cases hf : f T.head v with
    | false =>
      obtain ⟨d,hd,hfinal,hsilent⟩ := iht v T
      have he := inner_branch_step M b start f s t v T
      rw [hf] at he
      refine ⟨d,hd,?_,?_⟩
      · rw [same_advance _ _ _ he d hd]
        simpa [TM1.stepAux,hf] using hfinal
      · intro j hj
        rw [same_beep _ _ _ he]
        exact hsilent j hj
    | true =>
      obtain ⟨d,hd,hfinal,hsilent⟩ := ihs v T
      have he := inner_branch_step M b start f s t v T
      rw [hf] at he
      refine ⟨d,hd,?_,?_⟩
      · rw [same_advance _ _ _ he d hd]
        simpa [TM1.stepAux,hf] using hfinal
      · intro j hj
        rw [same_beep _ _ _ he]
        exact hsilent j hj
  | goto f =>
    refine ⟨1,by decide,?_,?_⟩
    · simp [EventSystem.advance,post,externalSystem,externalStep,inner,table,execute,encode,TM1.stepAux,Tape.write_self]
    · intro j hj
      have : j = 0 := by omega
      subst j
      simpa [EventSystem.BeepFrom,EventSystem.advance,inner_silent]
  | halt =>
    refine ⟨1,by decide,?_,?_⟩
    · simp [EventSystem.advance,post,externalSystem,externalStep,inner,table,execute,encode,TM1.stepAux,Tape.write_self]
    · intro j hj
      have : j = 0 := by omega
      subst j
      simpa [EventSystem.BeepFrom,EventSystem.advance,inner_silent]

theorem entry_same_next (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V)
    (q : L) (v : V) (T : Tape A) :
    ((post M b start).step (encode ⟨some q,v,T⟩)).1 =
      ((post M b start).step (inner (M q) v T)).1 := by
  rfl

theorem entry_flag (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V)
    (q : L) (v : V) (T : Tape A) :
    ((post M b start).step (encode ⟨some q,v,T⟩)).2 = b q := by
  cases h : execute (M q) T.head v with
  | mk p op => cases op <;> simp [post,externalSystem,externalStep,table,flags,encode,h]

/-- Every source transition has a positive finite post-Turing segment. The
only possible beep is on its first transition, and it matches the source. -/
theorem segment_exists (M : L → S) (b : L → Bool) (start x : TM1.Cfg A L V) :
    ∃ d, 0 < d ∧
      (post M b start).advance (encode x) d = encode ((source M b start).step x).1 ∧
      (∀ j, j < d → ((post M b start).BeepFrom (encode x) j ↔
        j = 0 ∧ ((source M b start).step x).2 = true)) := by
  cases x with
  | mk l v T =>
    cases l with
    | none =>
      refine ⟨1,by decide,?_,?_⟩
      · simp [source,post,externalSystem,externalStep,encode,table,flags,TM1.step,
          EventSystem.advance,Tape.write_self]
      · intro j hj
        have hj0 : j = 0 := by omega
        subst j
        simp [source,post,externalSystem,externalStep,encode,table,flags,TM1.step,
          EventSystem.BeepFrom,EventSystem.advance]
    | some q =>
      obtain ⟨d,hd,hfinal,hsilent⟩ := inner_finishes M b start (M q) v T
      have he := entry_same_next M b start q v T
      refine ⟨d,hd,?_,?_⟩
      · rw [same_advance_fst _ _ _ he d hd]
        simpa [source,TM1.step] using hfinal
      · intro j hj
        cases j with
        | zero =>
          simp [EventSystem.BeepFrom,EventSystem.advance,entry_flag,source]
        | succ j =>
          have hsil := hsilent (j+1) hj
          unfold EventSystem.BeepFrom at hsil ⊢
          rw [same_advance_fst _ _ _ he (j+1) (by omega)]
          simp [hsil]

noncomputable def duration (M : L → S) (b : L → Bool) (start x : TM1.Cfg A L V) : Nat := by
  classical
  exact Nat.find (segment_exists M b start x)

theorem duration_spec (M : L → S) (b : L → Bool) (start x : TM1.Cfg A L V) :
    0 < duration M b start x ∧
      (post M b start).advance (encode x) (duration M b start x) = encode ((source M b start).step x).1 ∧
      (∀ j, j < duration M b start x → ((post M b start).BeepFrom (encode x) j ↔
        j = 0 ∧ ((source M b start).step x).2 = true)) := by
  classical
  exact Nat.find_spec (segment_exists M b start x)

/-- A total post-Turing machine refines the full TM1 run, including an
explicit silent totalization of any halted TM1 configuration. -/
noncomputable def simulation (M : L → S) (b : L → Bool) (start : TM1.Cfg A L V) :
    SegmentSimulation (source M b start) (post M b start) where
  Rel := fun x y => y = encode x
  initial := rfl
  duration := fun x _ => duration M b start x
  positive := by intro x y h; exact (duration_spec M b start x).1
  next := by
    intro x y h
    subst y
    exact (duration_spec M b start x).2.1
  event_iff := by
    intro x y h
    subst y
    have hs := duration_spec M b start x
    constructor
    · intro hb
      exact ⟨0,hs.1,(hs.2.2 0 hs.1).2 ⟨rfl,hb⟩⟩
    · rintro ⟨j,hj,hb⟩
      exact ((hs.2.2 j hj).1 hb).2
  event_unique := by
    intro x y h j k hj hk hjb hkb
    subst y
    have hs := (duration_spec M b start x).2.2
    have hj0 := ((hs j hj).1 hjb).1
    have hk0 := ((hs k hk).1 hkb).1
    omega

def controllerPost (c : Code) := post (program1 c) flag1 initial1

/-- The two verified translations compose to carry the looping TM2
controller's events to the post-Turing model. -/
noncomputable def controllerRefinement (c : Code) :
    EventRefinement (ControllerTM2Loop.system c) (controllerPost c) :=
  (ControllerTM1Interior.refinement c).trans (simulation (program1 c) flag1 initial1).toEventRefinement

theorem pnp (c : Code) (hc : ControllerTM2Refinement.CodeCorrect Shared.PNP.TM2Candidate.compareSAT c) :
    (controllerPost c).EventuallySilent ↔
      ∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
        Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
          some (Shared.ComplexityBridge.CNF.sat x) :=
  ((simulation (program1 c) flag1 initial1).toEventRefinement.eventuallySilent_iff).symm.trans
    (ControllerTM1Interior.pnp c hc)

theorem npconp (c : Code) (hc : ControllerTM2Refinement.CodeCorrect Shared.NPCONP.TM2Verifier.compare c) :
    (controllerPost c).EventuallySilent ↔
      ∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
        Shared.NPCONP.TM2Verifier.test verifier x = true :=
  ((simulation (program1 c) flag1 initial1).toEventRefinement.eventuallySilent_iff).symm.trans
    (ControllerTM1Interior.npconp c hc)

end Shared.Beeping.MarkedTM1Post
