import Shared.PNP.Record285.FiniteTape
import Shared.PNP.Record285.OrdinaryEncoding
import Shared.PNP.Record285.PolynomialClock
import Shared.Codes.FiniteProgramTotalize

/-! The shared finite program's true-result tag as an ordinary marked event.
The input is supplied as a finite tape; no raw-input loader is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.PNP.Record285.FiniteProgramAdapter
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize
open Shared.PNP.Record285.FiniteTape
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.OrdinaryEncoding
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape

def count (p : Program) : Nat := p.length+3

def fallback : Shared.Codes.FinitePrograms.Row := (false,true,0,0)

def rawRow (p : Program) (q : Fin (count p)) (read : Bool) : Shared.Codes.FinitePrograms.Row :=
  match (totalProgram p)[q.val]? with
  | none => fallback
  | some rows => if read then rows.2 else rows.1

def physicalRow (p : Program) (r : Shared.Codes.FinitePrograms.Row) : Shared.Beeping.Machines.Row (count p) :=
  ⟨r.1, if r.2.1 then .right else .left,
    ⟨r.2.2.1 % count p, Nat.mod_lt _ (by simp [count])⟩,
    decide (r.2.2.1 % count p = trueState p)⟩

def machine (p : Program) : Machine (count p) :=
  ⟨⟨Vector.ofFn fun q => (physicalRow p (rawRow p q false), physicalRow p (rawRow p q true))⟩,
    ⟨0,by simp [count]⟩, false, 0⟩

@[simp] theorem machine_row (p : Program) (q : Fin (count p)) (read : Bool) :
    (machine p).table.row q read = physicalRow p (rawRow p q read) := by
  cases read <;> simp [machine, Table.row]

def ConfigRel (fc : Shared.Codes.FinitePrograms.Config) (mc : Shared.Beeping.Machines.Config (count p)) : Prop :=
  fc.1 = mc.state.val ∧ Rel fc.2 mc.tape mc.head

/-- One continuing finite-program step is one ordinary physical transition,
with the entire infinite blank-padded tape preserved. -/
theorem step_related (p : Program) (fc next : Shared.Codes.FinitePrograms.Config)
    (mc : Shared.Beeping.Machines.Config (count p))
    (hrel : ConfigRel fc mc)
    (hstep : Shared.Codes.FinitePrograms.step (totalProgram p) fc = some (.inr next))
    (hnext : next.1 < count p) :
    ConfigRel next ((machine p).step mc).1 := by
  rcases fc with ⟨q,L,b,R⟩
  rcases next with ⟨q',t'⟩
  rcases mc with ⟨state,head,tape⟩
  rcases hrel with ⟨hq,htape⟩
  dsimp only at hq htape
  have hread : tape head = b := htape.1
  cases hp : (totalProgram p)[q]? with
  | none => simp [Shared.Codes.FinitePrograms.step,hp] at hstep
  | some rows =>
    cases hb : b with
    | false =>
      simp only [Shared.Codes.FinitePrograms.step, hp, hb, Bool.false_eq_true, if_false] at hstep
      have hr : rawRow p state false = rows.1 := by simp [rawRow, ← hq, hp]
      cases htag : rows.1.2.2.2 with
      | zero =>
        simp only [htag, Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        simp only [Machine.step, machine_row, hread, hb, hr, physicalRow, ConfigRel]
        constructor
        · exact (Nat.mod_eq_of_lt hnext).symm
        · change Rel _ (writeAt tape head rows.1.1) _
          have htape' : Rel (L,false,R) tape head := by simpa [hb] using htape
          have hm := move_rel (L,false,R) tape head rows.1.1 (!rows.1.2.1) htape'
          cases hd : rows.1.2.1 <;>
            simpa [hd, Move.apply, Int.sub_eq_add_neg] using hm
      | succ tag =>
        cases tag with
        | zero => simp [htag] at hstep
        | succ k => cases k <;> simp_all
    | true =>
      simp only [Shared.Codes.FinitePrograms.step, hp, hb, if_true] at hstep
      have hr : rawRow p state true = rows.2 := by simp [rawRow, ← hq, hp]
      cases htag : rows.2.2.2.2 with
      | zero =>
        simp only [htag, Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        simp only [Machine.step, machine_row, hread, hb, hr, physicalRow, ConfigRel]
        constructor
        · exact (Nat.mod_eq_of_lt hnext).symm
        · change Rel _ (writeAt tape head rows.2.1) _
          have htape' : Rel (L,true,R) tape head := by simpa [hb] using htape
          have hm := move_rel (L,true,R) tape head rows.2.1 (!rows.2.2.1) htape'
          cases hd : rows.2.2.1 <;>
            simpa [hd, Move.apply, Int.sub_eq_add_neg] using hm
      | succ tag =>
        cases tag with
        | zero => simp [htag] at hstep
        | succ k => cases k <;> simp_all

/-- Every state used by the totalized simulation lies in its finite table. -/
theorem related_state_bound (p : Program) (s : Status)
    (c : Shared.Codes.FinitePrograms.Config) (h : Related p s c) : c.1 < count p := by
  cases s with
  | none => simp [Related, invalidState, count] at h ⊢; omega
  | some status =>
    cases status with
    | inl result =>
      cases result <;> simp [Related, falseState, trueState, count] at h ⊢ <;> omega
    | inr original =>
      by_cases ho : original.1 < p.length
      · simp [Related,ho] at h
        subst c
        simp [count]
        omega
      · simp [Related,ho,invalidState,count] at h ⊢
        omega

/-- The totalized initial list tape is related to the ordinary tape loaded
from the same low-endian word, including empty and trailing-false words. -/
theorem initial_related (p : Program) (word : List Bool) :
    ConfigRel (embed p (initial word)) (loaded (machine p) (value word)).initial := by
  constructor
  · simp [embed, initial, invalidState, loaded, machine]
  · exact initial_rel word

/-- Same-length totalized finite-program and ordinary runs remain related on
every tape cell, including cells beyond the represented finite lists. -/
theorem run_related (p : Program) (word : List Bool) (time : Nat) :
    ∃ d, run (totalProgram p) (embed p (initial word)) time = some (.inr d) ∧
      Related p (run p (initial word) time) d ∧
      ConfigRel d ((loaded (machine p) (value word)).run time) := by
  induction time with
  | zero => exact ⟨_, rfl, related_initial p _, initial_related p word⟩
  | succ time ih =>
    obtain ⟨d,hd,hstatus,htape⟩ := ih
    obtain ⟨d',hstep,hstatus'⟩ := related_step p _ d hstatus
    have hn : d'.1 < count p := related_state_bound p _ d' hstatus'
    refine ⟨d', ?_, ?_, ?_⟩
    · simp only [run_succ, hd, advance, hstep]
    · simpa only [run_succ] using hstatus'
    · change ConfigRel d' ((machine p).step ((loaded (machine p) (value word)).run time)).1
      exact step_related p d d' _ htape hstep hn

/-- The flag reports exactly that the next ordinary control is the true sink. -/
theorem beep_iff_next_true (p : Program) (word : List Bool) (time : Nat) :
    (loaded (machine p) (value word)).BeepAt time ↔
      ((loaded (machine p) (value word)).run (time+1)).state.val = trueState p := by
  rw [EventSystem.run_succ]
  change ((machine p).step ((loaded (machine p) (value word)).run time)).2 = true ↔
    ((machine p).step ((loaded (machine p) (value word)).run time)).1.state.val = trueState p
  simp [Machine.step, machine_row, physicalRow]

/-- A finite-program true result at a clock agrees with occupancy of the
ordinary true sink at that same clock. -/
theorem bounded_true_iff_state (p : Program) (word : List Bool) (time : Nat) :
    bounded p word time = some true ↔
      ((loaded (machine p) (value word)).run time).state.val = trueState p := by
  obtain ⟨d,_,hstatus,hrel⟩ := run_related p word time
  rw [bounded_true_iff_run, related_true_iff p _ d hstatus, hrel.1]

/-- Each marked ordinary transition corresponds to a true finite-program
result after exactly that transition. -/
theorem beep_iff_bounded_true (p : Program) (word : List Bool) (time : Nat) :
    (loaded (machine p) (value word)).BeepAt time ↔ bounded p word (time+1) = some true :=
  (beep_iff_next_true p word time).trans (bounded_true_iff_state p word (time+1)).symm

/-- The true-result tag occurs within a finite clock exactly when the ordinary
machine has emitted at least one marked event before that clock. -/
theorem bounded_true_iff_event (p : Program) (word : List Bool) (fuel : Nat) :
    bounded p word fuel = some true ↔
      ∃ time, time < fuel ∧ (loaded (machine p) (value word)).BeepAt time := by
  constructor
  · intro h
    cases fuel with
    | zero => simp [bounded, run] at h
    | succ time => exact ⟨time, by omega, (beep_iff_bounded_true p word time).2 h⟩
  · rintro ⟨time,ht,he⟩
    have h := (beep_iff_bounded_true p word time).1 he
    rw [bounded_true_iff_run] at h ⊢
    exact run_result_stable p (initial word) (by omega) h

/-- Numeric frame and canonical bit list are exactly the same natural stream. -/
theorem canonical_value (payload : List Bool) :
    value (canonical payload) = frame (2^payload.length) (value payload) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [value_bit]
  have h := frame_tape_canonical payload i
  change inputTape (frame (2^payload.length) (value payload)) (i : Int) = _ at h
  simpa [inputTape] using h.symm

/-- Every finite Boolean-result program is represented by one source program;
its true result on a canonical frame agrees at the source's exact clock.
False, invalid and timeout outcomes are all rejected. -/
theorem source_candidate_iff_bounded_true (p : Program) (exponent : Nat)
    (payload : List Bool) :
    candidate (Shared.PNP.Record285.UnaryProgram.finiteProgram (2*count p) (table (normalized (machine p)))) exponent
        payload.length (2^payload.length) (value payload) = true ↔
      bounded p (canonical payload) ((payload.length+2)^exponent) = some true := by
  rw [arbitrary_candidate_iff_loaded_event]
  rw [← canonical_value]
  exact (bounded_true_iff_event p (canonical payload) ((payload.length+2)^exponent)).symm

/-- A deterministic finite program cannot return two different results at
possibly different finite clocks. -/
theorem bounded_unique (p : Program) (word : List Bool) (a b : Nat) (x y : Bool)
    (hx : bounded p word a = some x) (hy : bounded p word b = some y) : x = y := by
  obtain ⟨tx,htx,hrx⟩ := (bounded_iff_result p word a x).1 hx
  obtain ⟨ty,hty,hry⟩ := (bounded_iff_result p word b y).1 hy
  have hx' := run_result_stable p (initial word) (Nat.le_max_left tx ty) hrx
  have hy' := run_result_stable p (initial word) (Nat.le_max_right tx ty) hry
  rw [hx'] at hy'
  simpa using hy'

/-- A finite Boolean-result decider on canonical frames with a pinned
polynomial clock is uniformly represented by one source candidate and one
positive exponent. The compiler producing that finite program remains an
explicit separate obligation. -/
theorem finite_program_canonical_coverage (p : Program) (answer : Nat → Nat → Bool)
    (bound : Polynomial Nat)
    (hcorrect : ∀ size payload, payload < 2^size →
      bounded p (canonical (bits size payload)) (bound.eval (2*size+1)) =
        some (answer size payload)) :
    ∃ program exponent, 0 < exponent ∧ ∀ size payload, payload < 2^size →
      (candidate program exponent size (2^size) payload = true ↔ answer size payload = true) := by
  apply Shared.PNP.Record285.PolynomialClock.finite_machine_canonical_polynomial_coverage
    (machine p) (fun size payload => answer size payload = true) bound
  · intro size payload hp time hevent
    let word := canonical (bits size payload)
    have hframe : value word = frame (2^size) payload := by
      simp [word, canonical_value, bits_length, value_bits_of_lt size payload hp]
    rw [← hframe] at hevent
    have htrue := (beep_iff_bounded_true p word time).1 hevent
    have hresult := hcorrect size payload hp
    change bounded p word _ = _ at hresult
    exact (bounded_unique p word _ _ true _ htrue hresult).symm
  · intro size payload hp hanswer
    let word := canonical (bits size payload)
    have hframe : value word = frame (2^size) payload := by
      simp [word, canonical_value, bits_length, value_bits_of_lt size payload hp]
    have hresult := hcorrect size payload hp
    change bounded p word _ = _ at hresult
    rw [hanswer] at hresult
    obtain ⟨t,ht,hevent⟩ := (bounded_true_iff_event p word _).1 hresult
    refine ⟨t,ht,?_⟩
    simpa [hframe] using hevent

/-- A polynomially bounded shared finite program for the exact reference
predicate implies silence of the abstract source controller. The existence
and correctness of that finite program are explicit premises. -/
theorem source_silent_of_finite_program (p : Program) (bound : Polynomial Nat)
    (hcorrect : ∀ size payload, payload < 2^size →
      bounded p (canonical (bits size payload)) (bound.eval (2*size+1)) =
        some (reference size (2^size) payload)) :
    controller.EventuallySilent := by
  obtain ⟨program,exponent,hpos,hcorrect'⟩ :=
    finite_program_canonical_coverage p (fun size payload => reference size (2^size) payload)
      bound hcorrect
  apply eventuallySilent_iff_goodCandidate.mpr
  refine ⟨program,exponent,hpos,?_⟩
  intro size payload hp
  have h := hcorrect' size payload hp
  unfold mismatch
  cases hc : candidate program exponent size (2^size) payload <;>
    cases hr : reference size (2^size) payload <;> simp_all

end Shared.PNP.Record285.FiniteProgramAdapter
