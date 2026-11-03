import Shared.Beeping.ComparisonJoined
import Shared.Beeping.Refinement

/-! Attach a single event-labelled commit transition to the joined evaluator.
The flag is a fixed finite-state row flag: it is true only on the `no` result
state. The handoff states are absorbing; resetting and starting the next
comparison remains a separate implementation obligation. -/
namespace Shared.Beeping.ComparisonCommit
open Turing Turing.PartrecToTM2
open Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.ComparisonTM2
open Shared.Beeping.ComparisonResultReader
open Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

variable {Λ : Type} [Inhabited Λ]
abbrev Q (Λ : Type) := (Λ ⊕ State) ⊕ Bool
instance : Inhabited (Q Λ) := ⟨.inr false⟩

def table (M : TM0.Machine Alphabet Λ) : TM0.Machine Alphabet (Q Λ)
  | .inl (.inr .no), a => some (.inr false, .write a)
  | .inl (.inr .yes), a => some (.inr true, .write a)
  | .inl q, a => match Shared.Beeping.ComparisonJoined.table M q a with
      | none => none
      | some (q', cmd) => some (.inl q',cmd)
  | .inr b, a => some (.inr b, .write a)

/-- The beep bit depends only on the current row's finite state. -/
def flag : Q Λ → Bool
  | .inl (.inr .no) => true
  | _ => false

def embed (c : TM0.Cfg Alphabet (Λ ⊕ State)) : TM0.Cfg Alphabet (Q Λ) := ⟨.inl c.q,c.Tape⟩
def handoff (b : Bool) (T : Tape Alphabet) : TM0.Cfg Alphabet (Q Λ) := ⟨.inr b,T⟩

/-- The evaluator and reader's finite support plus two handoff states. -/
def support [DecidableEq Λ] (S : Finset Λ) : Finset (Q Λ) :=
  (Shared.Beeping.ComparisonJoined.support S).image Sum.inl ∪ Finset.univ.image Sum.inr

theorem support_bound [DecidableEq Λ] (S : Finset Λ) :
    (support S).card ≤ S.card + 6 := by
  have hu := Finset.card_union_le
    ((Shared.Beeping.ComparisonJoined.support S).image (Sum.inl : (Λ ⊕ State) → Q Λ))
    (Finset.univ.image (Sum.inr : Bool → Q Λ))
  have h1 := Finset.card_image_le (s := Shared.Beeping.ComparisonJoined.support S)
    (f := (Sum.inl : (Λ ⊕ State) → Q Λ))
  have h2 := Finset.card_image_le (s := Finset.univ) (f := (Sum.inr : Bool → Q Λ))
  have hb := Shared.Beeping.ComparisonJoined.support_bound S
  have hh : (support S).card ≤ (Shared.Beeping.ComparisonJoined.support S).card + 2 := by
    simpa [support] using Nat.le_trans hu (Nat.add_le_add h1 h2)
  omega

theorem table_support [DecidableEq Λ] (M : TM0.Machine Alphabet Λ) (S : Finset Λ)
    (h : TM0.Supports M (S : Set Λ)) : TM0.Supports (table M) (support S : Set (Q Λ)) := by
  classical
  constructor
  · change Sum.inr false ∈ support S
    simp [support]
  · intro q a q' cmd hs hq
    cases q with
    | inr b =>
      simp [table] at hs
      obtain ⟨rfl,rfl⟩ := hs
      simp [support]
    | inl q =>
      cases q with
      | inl q =>
        have hq' : q ∈ S := by simpa [support,Shared.Beeping.ComparisonJoined.support] using hq
        cases hm : M q a with
        | none =>
          simp [table,Shared.Beeping.ComparisonJoined.table,hm] at hs
          obtain ⟨rfl,rfl⟩ := hs
          simp [support,Shared.Beeping.ComparisonJoined.support]
        | some p =>
          cases p with
          | mk dst action =>
            simp [table,Shared.Beeping.ComparisonJoined.table,hm] at hs
            obtain ⟨rfl,rfl⟩ := hs
            have hd : dst ∈ S := h.2 (by rw [hm]; rfl) hq'
            simp [support,Shared.Beeping.ComparisonJoined.support,hd]
      | inr st =>
        cases st with
        | no =>
          simp [table] at hs
          obtain ⟨rfl,rfl⟩ := hs
          simp [support]
        | yes =>
          simp [table] at hs
          obtain ⟨rfl,rfl⟩ := hs
          simp [support]
        | start =>
          simp [table,Shared.Beeping.ComparisonJoined.table,program] at hs
          obtain ⟨rfl,rfl⟩ := hs
          simp [support,Shared.Beeping.ComparisonJoined.support]
        | scan =>
          cases hb : readSymbol a <;>
            simp [table,Shared.Beeping.ComparisonJoined.table,program,hb] at hs <;>
            obtain ⟨rfl,rfl⟩ := hs <;>
            simp [support,Shared.Beeping.ComparisonJoined.support]

/-- Every table row, including the two handoff states, has a next step. -/
theorem table_total (M : TM0.Machine Alphabet Λ) (c : TM0.Cfg Alphabet (Q Λ)) :
    ∃ d, TM0.step (table M) c = some d := by
  cases c with
  | mk q T =>
    cases q with
    | inr b => simp [TM0.step,table]
    | inl q =>
      cases q with
      | inl q =>
        cases hm : M q T.head with
        | none => simp [TM0.step,table,Shared.Beeping.ComparisonJoined.table,hm]
        | some p =>
          cases p with
          | mk q' cmd =>
            cases cmd <;> simp [TM0.step,table,Shared.Beeping.ComparisonJoined.table,hm]
      | inr st => cases st <;> simp [TM0.step,table,Shared.Beeping.ComparisonJoined.table,program]

def system (M : TM0.Machine Alphabet Λ) (c : TM0.Cfg Alphabet Λ) : EventSystem (TM0.Cfg Alphabet (Q Λ)) where
  initial := embed (Shared.Beeping.ComparisonJoined.embed c)
  step x := ((TM0.step (table M) x).getD x, flag x.q)

theorem beep_iff (M : TM0.Machine Alphabet Λ) (c : TM0.Cfg Alphabet Λ) (t : Nat) :
    (system M c).BeepAt t ↔ flag ((system M c).run t).q = true := Iff.rfl

theorem source_step (M : TM0.Machine Alphabet Λ) (c d : TM0.Cfg Alphabet Λ)
    (h : TM0.step M c = some d) :
    TM0.step (table M) (embed (Shared.Beeping.ComparisonJoined.embed c)) =
      some (embed (Shared.Beeping.ComparisonJoined.embed d)) := by
  cases c with
  | mk q T =>
    cases hm : M q T.head with
    | none => simp [TM0.step,hm] at h
    | some p => cases p with
      | mk q' cmd =>
        simp only [TM0.step,hm,Option.map_some,Option.some.injEq] at h
        subst d
        cases cmd <;> simp [TM0.step,table,embed,Shared.Beeping.ComparisonJoined.embed,
          Shared.Beeping.ComparisonJoined.table,hm]

theorem terminal_step (M : TM0.Machine Alphabet Λ) (c : TM0.Cfg Alphabet Λ)
    (h : TM0.step M c = none) :
    TM0.step (table M) (embed (Shared.Beeping.ComparisonJoined.embed c)) =
      some ⟨.inl (.inr .scan),c.Tape.move Dir.right⟩ := by
  cases c with
  | mk q T =>
    cases hm : M q T.head with
    | none => simp [TM0.step,table,embed,Shared.Beeping.ComparisonJoined.embed,
        Shared.Beeping.ComparisonJoined.table,hm]
    | some p => simp [TM0.step,hm] at h

theorem scan_step (M : TM0.Machine Alphabet Λ) (T : Tape Alphabet) :
    TM0.step (table M) ⟨.inl (.inr .scan),T.move Dir.right⟩ =
      some ⟨.inl (.inr (resultState (readSymbol (T.move Dir.right).head))),T⟩ := by
  simp [TM0.step,table,Shared.Beeping.ComparisonJoined.table,program,resultState,Tape.move_right_left]

theorem commit_step (M : TM0.Machine Alphabet Λ) (b : Bool) (T : Tape Alphabet) :
    TM0.step (table M) ⟨.inl (.inr (resultState b)),T⟩ = some (handoff b T) := by
  cases b <;> simp [TM0.step,table,resultState,handoff,Tape.write_self]

theorem handoff_step (M : TM0.Machine Alphabet Λ) (b : Bool) (T : Tape Alphabet) :
    TM0.step (table M) (handoff b T) = some (handoff b T) := by
  simp [TM0.step,table,handoff,Tape.write_self]

theorem run_source (M : TM0.Machine Alphabet Λ) (initial final : TM0.Cfg Alphabet Λ) (n : Nat)
    (h : runSteps (TM0.step M) n initial = some final) :
    (system M initial).run n = embed (Shared.Beeping.ComparisonJoined.embed final) := by
  induction n generalizing final with
  | zero =>
    change some initial = some final at h
    cases Option.some.inj h
    rfl
  | succ n ih =>
    change (runSteps (TM0.step M) n initial).bind (TM0.step M) = some final at h
    cases hr : runSteps (TM0.step M) n initial with
    | none => simp [hr] at h
    | some mid =>
      have hm : TM0.step M mid = some final := by simpa [hr] using h
      rw [EventSystem.run_succ, ih mid hr]
      simp [system, source_step M mid final hm]

/-- Every prefix of a completed finite execution has a configuration. -/
theorem run_prefix {α : Type} (f : α → Option α) (a b : α) (d j : Nat)
    (h : runSteps f d a = some b) (hj : j ≤ d) :
    ∃ c, runSteps f j a = some c := by
  have he : d = j + (d-j) := by omega
  rw [he,runSteps_add] at h
  cases hr : runSteps f j a with
  | none => simp [hr] at h
  | some c => exact ⟨c,rfl⟩

/-- Exact finite trace: all evaluator and reader steps are silent, the
following commit beeps iff the comparison fails, and all later steps are
silent. The output tape is retained at the handoff. -/
theorem trace (M : TM0.Machine Alphabet Λ) (initial final : TM0.Cfg Alphabet Λ) (d : Nat)
    (hrun : runSteps (TM0.step M) d initial = some final) (hhalt : TM0.step M final = none)
    (b : Bool) (final1 : TM1.Cfg Alphabet Labels1 Store) (htape : final.Tape = final1.Tape)
    (hout : TM2to1.TrCfg (halt [if b then 1 else 0]) final1) :
    (∀ t, t < d + 2 → ¬ (system M initial).BeepAt t) ∧
    ((system M initial).BeepAt (d + 2) ↔ b = false) ∧
    (∀ k, (system M initial).run (d + 3 + k) = handoff b final.Tape) ∧
    (∀ t, d + 3 ≤ t → ¬ (system M initial).BeepAt t) := by
  have hresult := read_right b final1 hout
  rw [← htape] at hresult
  have hd := run_source M initial final d hrun
  have hd1 : (system M initial).run (d+1) = ⟨.inl (.inr .scan),final.Tape.move Dir.right⟩ := by
    rw [EventSystem.run_succ,hd]
    simp [system,terminal_step M final hhalt]
  have hd2 : (system M initial).run (d+2) = ⟨.inl (.inr (resultState b)),final.Tape⟩ := by
    rw [show d+2 = (d+1)+1 by omega,EventSystem.run_succ,hd1]
    simp [system,scan_step M final.Tape,hresult]
  have hd3 : (system M initial).run (d+3) = handoff b final.Tape := by
    rw [show d+3 = (d+2)+1 by omega,EventSystem.run_succ,hd2]
    simp [system,commit_step]
  have hafter : ∀ k, (system M initial).run (d+3+k) = handoff b final.Tape := by
    intro k
    induction k with
    | zero => simpa using hd3
    | succ k ih =>
      rw [Nat.add_succ,EventSystem.run_succ,ih]
      simp [system,handoff_step]
  refine ⟨?_,?_,hafter,?_⟩
  · intro t ht
    by_cases htd : t ≤ d
    · obtain ⟨c,hc⟩ := run_prefix (TM0.step M) initial final d t hrun htd
      have htc := run_source M initial c t hc
      rw [beep_iff,htc]
      simp [embed,Shared.Beeping.ComparisonJoined.embed,flag]
    · have he : t = d+1 := by omega
      subst t
      rw [beep_iff,hd1]
      simp [flag]
  · rw [beep_iff,hd2]
    cases b <;> simp [flag,resultState]
  · intro t ht
    have he : t = d+3+(t-(d+3)) := by omega
    rw [he]
    rw [beep_iff,hafter]
    simp [handoff,flag]

/-- The finite evaluator is followed by exactly one conditional commit beep,
with silent execution before and after it. This does not restart the controller. -/
def HasTrace (R : Nat → Nat → Bool) : Prop :=
  ∃ c : ToPartrec.Code,
    letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
    ∃ S : Finset (Q (TM1to0.Λ' program1)),
    TM0.Supports (table (program0 c)) (S : Set _) ∧
    ∀ e n, ∃ (d : Nat) (T : Tape Alphabet),
      (∀ t, t < d + 2 → ¬ (system (program0 c) (initial0 c [e,n])).BeepAt t) ∧
      ((system (program0 c) (initial0 c [e,n])).BeepAt (d + 2) ↔ R e n = false) ∧
      (∀ k, (system (program0 c) (initial0 c [e,n])).run (d + 3 + k) = handoff (R e n) T) ∧
      (∀ t, d + 3 ≤ t → ¬ (system (program0 c) (initial0 c [e,n])).BeepAt t)

theorem trace_of_singleTape (R : Nat → Nat → Bool)
    (h : Shared.Beeping.ComparisonSingleTape.Implements R) : HasTrace R := by
  classical
  obtain ⟨c,hc⟩ := h
  refine ⟨c, ?_⟩
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  refine ⟨support (support0 c), table_support (program0 c) (support0 c) hc.1, ?_⟩
  intro e n
  obtain ⟨final,hrel,hreach,hhalt⟩ := hc.2 e n
  obtain ⟨d,hd⟩ := reaches_runSteps hreach
  refine ⟨d,final.Tape, ?_⟩
  apply trace (program0 c) (initial0 c [e,n]) (TM1to0.trCfg program1 final)
    d hd hhalt (R e n) final rfl
  simpa [result] using hrel

theorem pnp : HasTrace Shared.PNP.TM2Candidate.compareSAT :=
  trace_of_singleTape _ pnp_has_singleTape

theorem npconp : HasTrace Shared.NPCONP.TM2Verifier.compare :=
  trace_of_singleTape _ npconp_has_singleTape

end Shared.Beeping.ComparisonCommit
