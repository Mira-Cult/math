import PASoundness.NumericCertificates
import PASoundness.Integration
import PASoundness.GenuineProducer

/-!
Literal contradiction search is separate from the nonhalting soundness master.
A total numeric checker is scanned in order. Any ordinary implementation of
that search can be converted to a finite partial-transition machine that halts
on its first true output row. The source equivalence is closed; an ordinary
search implementation is still a local simulation premise, not invented here.
-/
namespace PASoundness.ContradictionSearch
open Shared.Beeping Shared.Beeping.Machines Observer

def detected (code : Nat) : Bool :=
  decide (NumericCertificates.check code = some (⊥ : Peano.Formula))

theorem detected_exact : (∃ code, detected code = true) ↔
    Peano.Proves (⊥ : Peano.Sentence) := by
  simp only [detected, decide_eq_true_eq]
  exact NumericCertificates.check_exact _

def source : WordEventSystem Nat Bool where
  initial := 0
  step := fun code => (code+1, [detected code])

theorem source_run (t : Nat) : source.run t = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [WordEventSystem.run_succ, ih]; rfl

/-- A finite observation somewhere in the ordered output, not an observer
formula that decides the truth of a theory. -/
def Emits {C : Type} (system : WordEventSystem C Bool) (b : Bool) : Prop :=
  ∃ t, b ∈ system.prefixWord t

theorem emits_iff_step {C : Type} (system : WordEventSystem C Bool) (b : Bool) :
    Emits system b ↔ ∃ t, b ∈ (system.step (system.run t)).2 := by
  constructor
  · rintro ⟨t, ht⟩
    induction t with
    | zero => simpa using ht
    | succ t ih =>
      rw [WordEventSystem.prefix_succ, List.mem_append] at ht
      exact ht.elim ih (fun h => ⟨t, h⟩)
  · rintro ⟨t, ht⟩
    refine ⟨t+1, ?_⟩
    rw [WordEventSystem.prefix_succ, List.mem_append]
    exact Or.inr ht

theorem source_emits_iff_inconsistent : Emits source true ↔
    Peano.Proves (⊥ : Peano.Sentence) := by
  rw [emits_iff_step]
  apply Iff.trans _ detected_exact
  apply exists_congr
  intro t
  rw [source_run]
  simp [source]

theorem emits_preserved {S T : Type} {left : WordEventSystem S Bool}
    {right : WordEventSystem T Bool} (h : SameOutput left right) (b : Bool) :
    Emits left b ↔ Emits right b := by
  have transfer {A B : Type} {a : WordEventSystem A Bool} {c : WordEventSystem B Bool}
      (ht : ∀ w, a.OutputPrefix w → c.OutputPrefix w) : Emits a b → Emits c b := by
    rintro ⟨t, hb⟩
    obtain ⟨u, tail, hu⟩ := ht (a.prefixWord t) ⟨t, [], by simp⟩
    exact ⟨u, by rw [hu]; exact List.mem_append_left _ hb⟩
  exact ⟨transfer (fun w => (h w).mp), transfer (fun w => (h w).mpr)⟩

/-- An ordinary finite binary one-tape machine with absent transition rows
as literal halting. A present row writes, moves L/R, and changes finite state. -/
structure HaltingMachine (n : Nat) where
  rows : Vector (Option (Row n) × Option (Row n)) n
  start : Fin n
  blank : Bool
  startHead : Int

namespace HaltingMachine

def row {n : Nat} (M : HaltingMachine n) (q : Fin n) (read : Bool) : Option (Row n) :=
  if read then M.rows[q].2 else M.rows[q].1

def initial {n : Nat} (M : HaltingMachine n) : Config n :=
  ⟨M.start, M.startHead, fun _ => M.blank⟩

def step {n : Nat} (M : HaltingMachine n) (c : Config n) : Option (Config n) :=
  (M.row c.state (c.tape c.head)).map fun r =>
    ⟨r.next, r.move.apply c.head, c.write r.write⟩

def run {n : Nat} (M : HaltingMachine n) : Nat → Option (Config n)
  | 0 => some M.initial
  | t+1 => (M.run t).bind M.step

def Halts {n : Nat} (M : HaltingMachine n) : Prop := ∃ t, M.run t = none

end HaltingMachine

/-- Replace exactly the static BIT1 rows by halting. This does not inspect
arithmetic syntax or the tape beyond the ordinary read symbol. -/
def stopOnTrue {n : Nat} (M : Machine n) (labels : BitLabels n) : HaltingMachine n where
  rows := Vector.ofFn fun q =>
    ((if labels.at q false = some true then none else some (M.table.row q false)),
     (if labels.at q true = some true then none else some (M.table.row q true)))
  start := M.start
  blank := M.blank
  startHead := M.startHead

theorem stop_row {n : Nat} (M : Machine n) (labels : BitLabels n)
    (q : Fin n) (b : Bool) :
    (stopOnTrue M labels).row q b =
      if labels.at q b = some true then none else some (M.table.row q b) := by
  cases b <;> simp [stopOnTrue, HaltingMachine.row]

theorem stop_step {n : Nat} (M : Machine n) (labels : BitLabels n) (c : Config n) :
    (stopOnTrue M labels).step c =
      if labels.at c.state (c.tape c.head) = some true then none else some (M.step c).1 := by
  simp only [HaltingMachine.step, stop_row]
  split <;> rfl

theorem run_or_stopped {n : Nat} (M : Machine n) (labels : BitLabels n) (t : Nat) :
    (stopOnTrue M labels).run t = none ∨
      (stopOnTrue M labels).run t = some (M.system.run t) := by
  induction t with
  | zero => exact Or.inr rfl
  | succ t ih =>
    rcases ih with h | h
    · exact Or.inl (by simp [HaltingMachine.run, h])
    · rw [HaltingMachine.run, h, Option.bind_some, stop_step]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem stopped_has_true_row {n : Nat} (M : Machine n) (labels : BitLabels n)
    (t : Nat) (ht : (stopOnTrue M labels).run t = none) :
    ∃ s, labels.at (M.system.run s).state
      ((M.system.run s).tape (M.system.run s).head) = some true := by
  induction t with
  | zero => cases ht
  | succ t ih =>
    rcases run_or_stopped M labels t with h | h
    · exact ih h
    · rw [HaltingMachine.run, h, Option.bind_some, stop_step] at ht
      split at ht
      · exact ⟨t, ‹_›⟩
      · cases ht

theorem stop_halts_iff_true_row {n : Nat} (M : Machine n) (labels : BitLabels n) :
    (stopOnTrue M labels).Halts ↔
      ∃ t, labels.at (M.system.run t).state
        ((M.system.run t).tape (M.system.run t).head) = some true := by
  constructor
  · rintro ⟨t, ht⟩; exact stopped_has_true_row M labels t ht
  · rintro ⟨t, ht⟩
    rcases run_or_stopped M labels t with h | h
    · exact ⟨t, h⟩
    · exact ⟨t+1, by simp [HaltingMachine.run, h, stop_step, ht]⟩

theorem stop_halts_iff_emits {n : Nat} (M : Machine n) (labels : BitLabels n) :
    (stopOnTrue M labels).Halts ↔ Emits (machineWordSystem M labels) true := by
  rw [stop_halts_iff_true_row, emits_iff_step]
  apply exists_congr
  intro t
  rw [machineWordSystem_event]
  simp

/-- Conditional physical contradiction search, derived from the exact numeric
checker and a local implementation certificate, without assuming PA consistency. -/
theorem implementation_halts_iff_inconsistent {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate source M) :
    (stopOnTrue M cert.labels).Halts ↔ Peano.Proves (⊥ : Peano.Sentence) :=
  (stop_halts_iff_emits M cert.labels).trans
    ((emits_preserved cert.sameOutput true).symm.trans source_emits_iff_inconsistent)

/-- The master and contradiction search are different machines. Their shared
interpretation is literal PA falsity, under their separate certificates. -/
theorem master_zero_iff_search_halts (Z : Integration.ContradictionBridge)
    {masterStates searchStates : Nat} {master : Machine masterStates}
    {search : Machine searchStates}
    (masterCert : ImplementationCertificate Integration.source master)
    (searchCert : ImplementationCertificate source search) :
    Q_0 .compactSuffix
      (UnaryCodec.decodedEvents (UnaryCodec.eventTrace
        (machineWordSystem master masterCert.labels))) ↔
      (stopOnTrue search searchCert.labels).Halts :=
  (Integration.machine_levelZero_iff_inconsistent Z masterCert).trans
    (implementation_halts_iff_inconsistent searchCert).symm

/-- For the new genuine-PA source, the zero-channel theory bridge is closed.
The two physical implementation certificates remain independent obligations. -/
theorem genuine_master_zero_iff_search_halts
    {masterStates searchStates : Nat} {master : Machine masterStates}
    {search : Machine searchStates}
    (masterCert : ImplementationCertificate
      (GenuineProducer.source ArithmeticCertificates.pa) master)
    (searchCert : ImplementationCertificate source search) :
    Q_0 .compactSuffix (UniformMachine.events masterCert) ↔
      (stopOnTrue search searchCert.labels).Halts :=
  (GenuineProducer.machine_zero_iff_inconsistent ArithmeticCertificates.pa masterCert).trans
    (implementation_halts_iff_inconsistent searchCert).symm

end PASoundness.ContradictionSearch
