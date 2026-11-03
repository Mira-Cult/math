import Shared.PNP.Record285.UnaryReferenceTail

/-! Bounded nondeterministic computations only inspect their finite choice
prefix. This does not extend the computation clock or turn timeouts into rejects. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.WitnessTruncation
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.CanonicalInput

theorem choice_head_eq (a b clock : Nat) (h : a % 2^(clock+1) = b % 2^(clock+1)) :
    a%2 = b%2 := by
  have hd : 2 ∣ 2^(clock+1) := by
    rw [Nat.pow_succ]
    exact ⟨2^clock,by omega⟩
  have ha := Nat.mod_mod_of_dvd a hd
  have hb := Nat.mod_mod_of_dvd b hd
  rw [h] at ha
  omega

theorem choice_tail_eq (a b clock : Nat) (h : a % 2^(clock+1) = b % 2^(clock+1)) :
    (a/2) % 2^clock = (b/2) % 2^clock := by
  have hh := congrArg (fun x : Nat => x/2) h
  simpa only [Nat.pow_succ,Nat.mod_mul_left_div_self] using hh

/-- A step sees only the low choice bit; the two outputs differ only in the
unconsumed high choice suffix. -/
theorem simStep_choices (program : Nat) (s : SimState) (a b : Nat) (h : a%2=b%2) :
    simStep program {s with choices := a} =
      (simStep program {s with choices := b}).map (fun t => {t with choices := a/2}) := by
  simp only [simStep,h]
  split <;> rfl

/-- HALT within exactly the same bound depends only on the first `clock`
choice bits, for every program and arbitrary virtual configuration. -/
theorem haltedWithin_choice_congr (program clock : Nat) (s : SimState) (a b : Nat)
    (h : a % 2^clock = b % 2^clock) :
    haltedWithin program clock {s with choices := a} =
      haltedWithin program clock {s with choices := b} := by
  induction clock generalizing s a b with
  | zero => rfl
  | succ clock ih =>
    have hh := choice_head_eq a b clock h
    have ht := choice_tail_eq a b clock h
    have hs := simStep_choices program s a b hh
    cases hb : simStep program {s with choices := b} with
    | none =>
      simp only [hb,Option.map_none] at hs
      simp [haltedWithin,hs,hb]
    | some next =>
      simp only [hb,Option.map_some] at hs
      have hnext : next.choices = b/2 := by
        simp only [simStep] at hb
        split at hb
        · contradiction
        · cases hb
          rfl
      simp only [haltedWithin,hs,hb]
      have hi := ih next (a/2) (b/2) ht
      have heq : {next with choices := b/2} = next := by
        cases next; simp_all
      rw [heq] at hi
      exact hi

/-- Truncating to precisely the original clock preserves the bounded result,
including a timeout or a HALT on its last permitted transition. -/
theorem haltedWithin_truncate (program clock : Nat) (s : SimState) :
    haltedWithin program clock s =
      haltedWithin program clock {s with choices := s.choices % 2^clock} := by
  have h := haltedWithin_choice_congr program clock s s.choices (s.choices % 2^clock) (by simp)
  simpa using h

/-- A finite-table step also depends only on the low choice bit; the map
keeps its complete physical tape, absolute head and facing unchanged. -/
theorem finiteStep_choices {n : Nat} (f : Fin n → Bool → Bool → FiniteAction n)
    (c : FiniteConfig n) (a b : Nat) (h : a%2=b%2) :
    finiteStep f {c with choices := a} =
      (finiteStep f {c with choices := b}).map (fun t => {t with choices := a/2}) := by
  have hb : a.testBit 0 = b.testBit 0 := by
    simp only [Nat.testBit_zero,h]
  simp only [finiteStep,hb]
  cases (f c.state (c.physical.tape c.physical.head) (b.testBit 0)).next <;> rfl

/-- A bounded finite-table run with the same relevant choice prefix has the
same live state and *entire* physical tape/head/facing, or both runs halt. -/
theorem finiteRun_choices {n : Nat} (f : Fin n → Bool → Bool → FiniteAction n)
    (clock : Nat) (c : FiniteConfig n) (a b : Nat) (h : a%2^clock=b%2^clock) :
    (finiteRun f clock {c with choices := a}).map (fun t => (t.state,t.physical)) =
      (finiteRun f clock {c with choices := b}).map (fun t => (t.state,t.physical)) := by
  induction clock generalizing c a b with
  | zero => rfl
  | succ clock ih =>
    have hh := choice_head_eq a b clock h
    have ht := choice_tail_eq a b clock h
    have hs := finiteStep_choices f c a b hh
    cases hb : finiteStep f {c with choices := b} with
    | none =>
      simp only [hb,Option.map_none] at hs
      simp [finiteRun,hs,hb]
    | some next =>
      simp only [hb,Option.map_some] at hs
      have hnext : next.choices = b/2 := by
        simp only [finiteStep] at hb
        cases he : (f c.state (c.physical.tape c.physical.head) (b.testBit 0)).next with
        | none =>
          simp only [he,Option.map_none] at hb
          cases hb
        | some q =>
          simp only [he,Option.map_some,Option.some.injEq] at hb
          cases hb
          rfl
      simp only [finiteRun,hs,hb]
      have hi := ih next (a/2) (b/2) ht
      have heq : {next with choices := b/2} = next := by cases next; simp_all
      rw [heq] at hi
      exact hi

/-- In particular, high choice bits cannot alter any live tape cell or head
position before the specified clock. -/
theorem finiteRun_truncate {n : Nat} (f : Fin n → Bool → Bool → FiniteAction n)
    (clock : Nat) (c : FiniteConfig n) :
    (finiteRun f clock c).map (fun t => (t.state,t.physical)) =
      (finiteRun f clock {c with choices := c.choices % 2^clock}).map (fun t => (t.state,t.physical)) := by
  have h := finiteRun_choices f clock c c.choices (c.choices % 2^clock) (by simp)
  simpa using h

/-- The finite-table HALT predicate is the same bounded source predicate,
with no loss of the complete tape/head relation in the underlying run. -/
theorem finite_halt_iff_source (n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (clock input branch : Nat) :
    finiteRun f clock (finiteInitial hn input branch) = none ↔
      haltedWithin (finiteProgram n f) clock (initialSim input branch) = true := by
  have hh := finiteRun_encoded f clock (finiteInitial hn input branch)
  rw [embed_finiteInitial] at hh
  rw [initial_halted_iff,←hh]
  cases finiteRun f clock (finiteInitial hn input branch) <;> simp

/-- Truncating choices preserves the exact bounded finite-table result. -/
theorem finite_halt_truncate (n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (clock input branch : Nat) :
    (finiteRun f clock (finiteInitial hn input branch) = none ↔
      finiteRun f clock (finiteInitial hn input (branch % 2^clock)) = none) := by
  rw [finite_halt_iff_source n hn f,finite_halt_iff_source n hn f]
  have hh := haltedWithin_truncate (finiteProgram n f) clock (initialSim input branch)
  simpa [initialSim] using congrArg (fun x => x = true) hh

/-- For a fixed clock, an unrestricted finite choice stream exists exactly
when one exists below the source's `2^clock` cutoff. -/
theorem finite_halt_unbounded_choices (n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (clock input : Nat) :
    (∃ branch, finiteRun f clock (finiteInitial hn input branch) = none) ↔
      ∃ branch, branch < 2^clock ∧ finiteRun f clock (finiteInitial hn input branch) = none := by
  constructor
  · rintro ⟨branch,haccept⟩
    refine ⟨branch % 2^clock,Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)),?_⟩
    exact (finite_halt_truncate n hn f clock input branch).1 haccept
  · rintro ⟨branch,_,haccept⟩
    exact ⟨branch,haccept⟩

/-- The reference's witness cutoff loses no bounded finite-table behavior;
this does not change its clock or identify a timed-out result at a later time. -/
theorem referenceLanguage_finite_unbounded_choices (n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let clock := tableWidth n f+padding
    referenceLanguage (canonical (bits clock (finiteProgram n f))) = true ↔
      ∃ branch, finiteRun f clock (finiteInitial hn 0 branch) = none := by
  dsimp only
  exact (referenceLanguage_embeds_finite n hn f padding).trans
    (finite_halt_unbounded_choices n hn f (tableWidth n f+padding) 0).symm

/-- Numeric source choices are equivalent to a conventional Boolean-list
witness of length at most the exact clock. The witness is read low bit first. -/
theorem finite_halt_iff_list_witness (n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (clock input : Nat) :
    (∃ branch, finiteRun f clock (finiteInitial hn input branch) = none) ↔
      ∃ witness : List Bool, witness.length ≤ clock ∧
        finiteRun f clock (finiteInitial hn input (value witness)) = none := by
  constructor
  · intro h
    obtain ⟨branch,hbound,haccept⟩ := (finite_halt_unbounded_choices n hn f clock input).1 h
    refine ⟨bits clock branch,by simp,?_⟩
    rw [value_bits_of_lt clock branch hbound]
    exact haccept
  · rintro ⟨witness,_,haccept⟩
    exact ⟨value witness,haccept⟩

/-- The reference's exact finite-table frame searches precisely the usual
bounded Boolean-list witnesses at the same clock. -/
theorem referenceLanguage_finite_list_witness (n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let clock := tableWidth n f+padding
    referenceLanguage (canonical (bits clock (finiteProgram n f))) = true ↔
      ∃ witness : List Bool, witness.length ≤ clock ∧
        finiteRun f clock (finiteInitial hn 0 (value witness)) = none := by
  dsimp only
  exact (referenceLanguage_finite_unbounded_choices n hn f padding).trans
    (finite_halt_iff_list_witness n hn f (tableWidth n f+padding) 0)

/-- Regression for timeout sensitivity: one fixed source program times out
after one step and halts on its second, so extending the clock is not neutral. -/
theorem timeout_can_turn_into_halt :
    haltedWithin 255 1 (initialSim 0 0) = false ∧
      haltedWithin 255 2 (initialSim 0 0) = true := by
  simp [haltedWithin,simStep,initialSim,skipUnary,popUnary]

end Shared.PNP.Record285.WitnessTruncation
