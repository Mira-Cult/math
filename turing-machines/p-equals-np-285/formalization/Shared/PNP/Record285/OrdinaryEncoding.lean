import Shared.PNP.Record285.UnaryProgram
import Shared.Beeping.Machines
import Shared.PNP.Record285.Quotient

/-! Encode finite ordinary binary machines as relative source candidates.
The ordinary machine begins at state zero on a supplied canonical frame;
this is not a blank-tape loader or a complexity-model compiler. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.PNP.Record285.OrdinaryEncoding
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.Quotient

def control (q : Fin n) (left : Bool) : Fin (2*n) :=
  ⟨2*q.val + if left then 1 else 0, by have h := q.isLt; cases left <;> simp <;> omega⟩

def state (q : Fin (2*n)) : Fin n := ⟨q.val / 2, by have h := q.isLt; omega⟩
def facing (q : Fin (2*n)) : Bool := decide (q.val % 2 = 1)

theorem state_control (q : Fin n) (left : Bool) : state (control q left) = q := by
  apply Fin.ext
  cases left <;> simp [state, control] <;> omega

theorem facing_control (q : Fin n) (left : Bool) : facing (control q left) = left := by
  cases left <;> simp [facing, control]

def leftMove : Move → Bool | .left => true | .right => false

def table (M : Machine n) (q : Fin (2*n)) (read _choice : Bool) : FiniteAction (2*n) :=
  let row := M.table.row (state q) read
  let nextFacing := leftMove row.move
  ⟨row.write, facing q != nextFacing,
    if row.beep then none else some (control row.next nextFacing)⟩

def lift (c : Config n) (left : Bool) : FiniteConfig (2*n) :=
  ⟨control c.state left, ⟨c.tape, c.head, left⟩, 0⟩

/-- One ordinary step is one source-relative step, with identical complete
live tapes and heads; a marked transition becomes HALT. -/
theorem step (M : Machine n) (c : Config n) (left : Bool) :
    finiteStep (table M) (lift c left) =
      if (M.step c).2 then none
      else some (lift (M.step c).1 (leftMove (M.table.row c.state (c.tape c.head)).move)) := by
  cases c with
  | mk q head tape =>
    simp only [finiteStep, table, lift, state_control, facing_control, Machine.step]
    cases left <;> cases hm : (M.table.row q (tape head)).move <;>
      cases hb : (M.table.row q (tape head)).beep <;>
        simp [leftMove, physicalStep, Move.apply, Int.sub_eq_add_neg] <;> rfl

/-- A conventional machine initialized on a supplied framed tape. -/
def loaded (M : Machine n) (input : Nat) : EventSystem (Config n) :=
  ⟨⟨M.start, 0, inputTape input⟩, M.step⟩

def startingAt (M : Machine n) (c : Config n) : EventSystem (Config n) := ⟨c, M.step⟩

theorem startingAt_run_succ (M : Machine n) (c : Config n) (t : Nat) :
    (startingAt M (M.step c).1).run t = (startingAt M c).run (t+1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [EventSystem.run_succ, ih]
    rfl

/-- A live relative run corresponds to the full ordinary configuration. -/
theorem finiteRun_live (M : Machine n) (c : Config n) (left : Bool)
    (clock : Nat) (current : FiniteConfig (2*n))
    (hrun : finiteRun (table M) clock (lift c left) = some current) :
    ∃ nextLeft, current = lift ((startingAt M c).run clock) nextLeft := by
  induction clock generalizing c left current with
  | zero =>
    simp only [finiteRun, Option.some.injEq] at hrun
    subst current
    exact ⟨left,rfl⟩
  | succ clock ih =>
    simp only [finiteRun, step] at hrun
    cases hb : (M.step c).2 with
    | true => simp [hb] at hrun
    | false =>
      simp only [hb, Bool.false_eq_true, if_false] at hrun
      obtain ⟨nextLeft,hnext⟩ := ih (M.step c).1 _ current hrun
      refine ⟨nextLeft, ?_⟩
      simpa only [startingAt_run_succ] using hnext

theorem finiteRun_succ_last (f : Fin n → Bool → Bool → FiniteAction n)
    (clock : Nat) (c : FiniteConfig n) :
    finiteRun f (clock+1) c = (finiteRun f clock c).bind (finiteStep f) := by
  induction clock generalizing c with
  | zero => cases hs : finiteStep f c <;> simp [finiteRun, hs]
  | succ clock ih =>
    simp only [finiteRun]
    cases hs : finiteStep f c with
    | none => rfl
    | some next => exact ih next

/-- On every finite prefix, the relative machine halts exactly when the
ordinary machine has taken a marked transition. -/
theorem finiteRun_iff_event (M : Machine n) (c : Config n) (left : Bool)
    (clock : Nat) :
    finiteRun (table M) clock (lift c left) = none ↔
      ∃ t, t < clock ∧ (startingAt M c).BeepAt t := by
  induction clock with
  | zero => simp [finiteRun]
  | succ clock ih =>
    rw [finiteRun_succ_last]
    cases hp : finiteRun (table M) clock (lift c left) with
    | none =>
      have hevents := ih.mp hp
      simp only [Option.bind_none, true_iff]
      obtain ⟨t,ht,he⟩ := hevents
      exact ⟨t, by omega, he⟩
    | some previous =>
      have hnoprev : ¬ ∃ t, t < clock ∧ (startingAt M c).BeepAt t := by
        intro he
        have h := ih.mpr he
        rw [hp] at h
        contradiction
      obtain ⟨nextLeft,hlive⟩ := finiteRun_live M c left clock previous hp
      subst previous
      rw [Option.bind_some, step]
      cases hb : (M.step ((startingAt M c).run clock)).2 with
      | true =>
        simp only [if_true, true_iff]
        exact ⟨clock, by omega, hb⟩
      | false =>
        simp only [Bool.false_eq_true, if_false, Option.some_ne_none, false_iff]
        rintro ⟨t,ht,he⟩
        by_cases h : t = clock
        · subst t
          change (M.step ((startingAt M c).run clock)).2 = true at he
          rw [hb] at he
          contradiction
        · exact hnoprev ⟨t, by omega, he⟩

/-- When the ordinary start state is numbered zero, the source candidate's
initial finite control is exactly its loaded initial configuration. -/
theorem initial_eq (M : Machine n) (hstart : M.start.val = 0) (input : Nat) :
    finiteInitial (by have := M.start.isLt; omega : 0 < 2*n) input 0 =
      lift (loaded M input).initial false := by
  have hpos : 0 < n := by have h := M.start.isLt; omega
  have hstate : M.start = ⟨0,hpos⟩ := Fin.ext hstart
  simp [finiteInitial, lift, loaded, control, hstate]

/-- Every zero-start ordinary finite binary machine has a uniform source
program whose candidate result is exactly whether the machine emitted on the
supplied frame before the candidate's original polynomial clock expired. -/
theorem candidate_iff_loaded_event (M : Machine n) (hstart : M.start.val = 0)
    (exponent size radix remaining : Nat) :
    Source.candidate (finiteProgram (2*n) (table M)) exponent size radix remaining = true ↔
      ∃ t, t < (size+2)^exponent ∧
        (loaded M (Source.frame radix remaining)).BeepAt t := by
  have hpos : 0 < 2*n := by have h := M.start.isLt; omega
  rw [finite_candidate_iff hpos, initial_eq M hstart]
  exact finiteRun_iff_event M (loaded M (Source.frame radix remaining)).initial false _

/-- Swap the ordinary start state with zero; the map is its own inverse. -/
def zeroState (M : Machine n) : Fin n := ⟨0, by have := M.start.isLt; omega⟩

def swapStart (M : Machine n) (q : Fin n) : Fin n :=
  if q = M.start then zeroState M else if q = zeroState M then M.start else q

@[simp] theorem swap_start (M : Machine n) : swapStart M M.start = zeroState M := by
  simp [swapStart]

@[simp] theorem swap_zero (M : Machine n) : swapStart M (zeroState M) = M.start := by
  by_cases h : M.start = zeroState M
  · simp [swapStart, h]
  · simp [swapStart, Ne.symm h]

@[simp] theorem swap_involutive (M : Machine n) (q : Fin n) :
    swapStart M (swapStart M q) = q := by
  by_cases hstart : q = M.start
  · subst q; simp
  · by_cases hzero : q = zeroState M
    · subst q; simp
    · simp [swapStart, hstart, hzero]

def renamedRow (M : Machine n) (q : Fin n) (read : Bool) : Row n :=
  mappedRow (swapStart M) (M.table.row (swapStart M q) read)

def normalized (M : Machine n) : Machine n :=
  ⟨⟨Vector.ofFn fun q => (renamedRow M q false, renamedRow M q true)⟩,
    zeroState M, M.blank, M.startHead⟩

@[simp] theorem normalized_row (M : Machine n) (q : Fin n) (read : Bool) :
    (normalized M).table.row q read = renamedRow M q read := by
  cases read <;> simp [normalized, Table.row]

theorem normalization_correct (M : Machine n) : Correct M (normalized M) (swapStart M) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · simp [normalized]
  · intro q b
    simp [renamedRow]

/-- The renaming preserves the complete run on any supplied input frame. -/
theorem loaded_related (M : Machine n) (input time : Nat) :
    ConfigRel (swapStart M) ((loaded M input).run time)
      ((loaded (normalized M) input).run time) := by
  induction time with
  | zero =>
    refine ⟨?_, rfl, rfl⟩
    exact (normalization_correct M).start
  | succ time ih => exact (step_related (normalization_correct M) _ _ ih).1

theorem loaded_beep_iff (M : Machine n) (input time : Nat) :
    (loaded (normalized M) input).BeepAt time ↔ (loaded M input).BeepAt time := by
  change ((normalized M).step ((loaded (normalized M) input).run time)).2 = true ↔
    (M.step ((loaded M input).run time)).2 = true
  rw [(step_related (normalization_correct M) _ _ (loaded_related M input time)).2]

/-- Any ordinary finite binary machine, regardless of its original state
numbering, has a source candidate with the same bounded marked-event test on
the supplied frame. -/
theorem arbitrary_candidate_iff_loaded_event (M : Machine n)
    (exponent size radix remaining : Nat) :
    Source.candidate (finiteProgram (2*n) (table (normalized M))) exponent size radix remaining = true ↔
      ∃ t, t < (size+2)^exponent ∧
        (loaded M (Source.frame radix remaining)).BeepAt t := by
  have hstart : (normalized M).start.val = 0 := rfl
  rw [candidate_iff_loaded_event (normalized M) hstart]
  constructor <;> rintro ⟨t,ht,he⟩ <;> refine ⟨t,ht,?_⟩
  · exact (loaded_beep_iff M _ t).1 he
  · exact (loaded_beep_iff M _ t).2 he

end Shared.PNP.Record285.OrdinaryEncoding
