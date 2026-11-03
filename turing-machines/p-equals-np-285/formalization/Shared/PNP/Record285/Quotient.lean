import Shared.Beeping.Machines
import Shared.Beeping.Refinement

/-! A finite, event-coloured quotient checker. Its hypotheses include *every*
source state and both input rows, including all preimages of a quotient state.
No claim is made here that a particular record-table certificate passes it. -/
namespace Shared.PNP.Record285.Quotient
open Shared.Beeping
open Shared.Beeping.Machines

def mappedRow {n m : Nat} (f : Fin n → Fin m) (r : Row n) : Row m :=
  ⟨r.write, r.move, f r.next, r.beep⟩

/-- `target` is an exact event-coloured quotient of `source`. -/
structure Correct {n m : Nat} (source : Machine n) (target : Machine m)
    (f : Fin n → Fin m) : Prop where
  start : target.start = f source.start
  blank : target.blank = source.blank
  head : target.startHead = source.startHead
  row : ∀ q b, target.table.row (f q) b = mappedRow f (source.table.row q b)

/-- Executable finite check. Both input symbols are checked for every source
state; this includes all distinct raw-state preimages of merged states. -/
def check {n m : Nat} (source : Machine n) (target : Machine m)
    (f : Fin n → Fin m) : Bool :=
  decide (target.start = f source.start) && decide (target.blank = source.blank) &&
  decide (target.startHead = source.startHead) &&
  (List.finRange n).all fun q =>
    decide (target.table.row (f q) false = mappedRow f (source.table.row q false)) &&
    decide (target.table.row (f q) true = mappedRow f (source.table.row q true))

theorem check_sound {n m : Nat} (source : Machine n) (target : Machine m)
    (f : Fin n → Fin m) (h : check source target f = true) : Correct source target f := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hstart,hblank⟩,hhead⟩,hrows⟩
  refine ⟨hstart,hblank,hhead,?_⟩
  intro q b
  have hr := (List.all_eq_true.mp hrows) q (List.mem_finRange q)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  cases b with
  | false => exact hr.1
  | true => exact hr.2


theorem check_complete {n m : Nat} (source : Machine n) (target : Machine m)
    (f : Fin n → Fin m) (h : Correct source target f) : check source target f = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨h.start,h.blank⟩,h.head⟩, ?_⟩
  intro q _
  exact ⟨h.row q false, h.row q true⟩

theorem check_iff_correct {n m : Nat} (source : Machine n) (target : Machine m)
    (f : Fin n → Fin m) : check source target f = true ↔ Correct source target f :=
  ⟨check_sound source target f, check_complete source target f⟩

def ConfigRel {n m : Nat} (f : Fin n → Fin m) (a : Config n) (b : Config m) : Prop :=
  b.state = f a.state ∧ b.head = a.head ∧ b.tape = a.tape

theorem initial_related {n m : Nat} {source : Machine n} {target : Machine m}
    {f : Fin n → Fin m} (h : Correct source target f) :
    ConfigRel f source.initial target.initial := by
  refine ⟨h.start,h.head,?_⟩
  funext p
  exact h.blank

/-- One source step and one quotient step have identical write, move and flag,
and the complete tapes and head positions remain related. -/
theorem step_related {n m : Nat} {source : Machine n} {target : Machine m}
    {f : Fin n → Fin m} (h : Correct source target f)
    (a : Config n) (b : Config m) (hab : ConfigRel f a b) :
    ConfigRel f (source.step a).1 (target.step b).1 ∧
      (target.step b).2 = (source.step a).2 := by
  rcases a with ⟨q,head,tape⟩
  rcases b with ⟨r,head',tape'⟩
  rcases hab with ⟨hs,hh,ht⟩
  dsimp only at hs hh ht
  subst r
  subst head'
  subst tape'
  simp [Machine.step, h.row, mappedRow, ConfigRel]
  rfl

theorem run_related {n m : Nat} {source : Machine n} {target : Machine m}
    {f : Fin n → Fin m} (h : Correct source target f) (t : Nat) :
    ConfigRel f (source.system.run t) (target.system.run t) := by
  induction t with
  | zero => exact initial_related h
  | succ t ih => exact (step_related h _ _ ih).1

theorem beep_iff {n m : Nat} {source : Machine n} {target : Machine m}
    {f : Fin n → Fin m} (h : Correct source target f) (t : Nat) :
    target.system.BeepAt t ↔ source.system.BeepAt t := by
  change (target.step (target.system.run t)).2 = true ↔
    (source.step (source.system.run t)).2 = true
  rw [(step_related h _ _ (run_related h t)).2]

theorem eventuallySilent_iff {n m : Nat} {source : Machine n} {target : Machine m}
    {f : Fin n → Fin m} (h : Correct source target f) :
    target.system.EventuallySilent ↔ source.system.EventuallySilent := by
  constructor <;> rintro ⟨T,hT⟩ <;> refine ⟨T,?_⟩ <;> intro t ht hb
  · exact hT t ht ((beep_iff h t).2 hb)
  · exact hT t ht ((beep_iff h t).1 hb)


/-- A checked quotient is a one-for-one progress-sensitive refinement with an
identity boundary map. Every full tape, head and event is preserved. -/
def refinement {n m : Nat} {source : Machine n} {target : Machine m}
    {f : Fin n → Fin m} (h : Correct source target f) :
    EventRefinement source.system target.system where
  Rel := ConfigRel f
  boundary := id
  boundary_zero := rfl
  progress := by intro i; simp
  related := by intro i; exact run_related h i
  event_iff := by
    intro i
    constructor
    · intro hb
      exact ⟨i, by simp, by simp, (beep_iff h i).2 hb⟩
    · rintro ⟨j,hlo,hhi,hb⟩
      have heq : j = i := by simp only [id_eq] at hlo hhi; omega
      subst j
      exact (beep_iff h i).1 hb
  event_unique := by
    intro i j k hjlo hjhi hklo hkhi _ _
    simp only [id_eq] at hjlo hjhi hklo hkhi
    omega

/-- An entry event occurs one step before the corresponding B-exit event. -/
theorem entering_exiting_shift {n : Nat} (M : Machine n) (B : Fin n) (t : Nat) :
    (M.entering B).system.BeepAt t ↔ (M.exiting B).system.BeepAt (t+1) := by
  rw [Machine.entering_beep_iff, Machine.exiting_beep_iff]

theorem entering_exiting_silence {n : Nat} (M : Machine n) (B : Fin n) :
    (M.entering B).system.EventuallySilent ↔ (M.exiting B).system.EventuallySilent := by
  constructor
  · rintro ⟨T,hT⟩
    refine ⟨T+1,?_⟩
    intro t ht hb
    have heq : t - 1 + 1 = t := by omega
    apply hT (t-1) (by omega)
    apply (entering_exiting_shift M B (t-1)).2
    simpa [heq] using hb
  · rintro ⟨T,hT⟩
    refine ⟨T,?_⟩
    intro t ht hb
    exact hT (t+1) (by omega) ((entering_exiting_shift M B t).1 hb)

/-- If the finite checker certifies the B-ingress quotient, the marked target's
finite/infinite event behavior is exactly the B-exit companion's. -/
theorem checked_ingress_exit_silence {n m : Nat} (source : Machine n) (target : Machine m)
    (B : Fin n) (f : Fin n → Fin m) (h : check (source.entering B) target f = true) :
    target.system.EventuallySilent ↔ (source.exiting B).system.EventuallySilent :=
  (eventuallySilent_iff (check_sound _ _ _ h)).trans (entering_exiting_silence source B)

theorem checked_ingress_exit_infinite {n m : Nat} (source : Machine n) (target : Machine m)
    (B : Fin n) (f : Fin n → Fin m) (h : check (source.entering B) target f = true) :
    target.system.InfinitelyManyBeeps ↔ (source.exiting B).system.InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    ← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    checked_ingress_exit_silence source target B f h]

end Shared.PNP.Record285.Quotient
