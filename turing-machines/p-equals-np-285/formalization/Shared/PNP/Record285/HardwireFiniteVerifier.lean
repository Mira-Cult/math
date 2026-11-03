import Shared.PNP.Record285.HardwireChoiceLoader
import Shared.PNP.Record285.FiniteProgramAdapter

/-! Compose the hardwired public/witness loader with an actual finite Boolean
verifier, including its totalized true-result sink and exact clock. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HardwireFiniteVerifier
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.Codes.FinitePrograms
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.OrdinaryEncoding
open Shared.PNP.Record285.FiniteProgramAdapter
open Shared.PNP.Record285.HardwireChoiceLoader

def states (p : Program) : Nat := 2*FiniteProgramAdapter.count p

def relativeTable (p : Program) : Fin (states p) → Bool → Bool → FiniteAction (states p) :=
  OrdinaryEncoding.table (FiniteProgramAdapter.machine p)

theorem states_positive (p : Program) : 0 < states p := by simp [states,FiniteProgramAdapter.count]

/-- A deterministic ordinary table does not observe the source's choice bit. -/
theorem ordinary_step_choices {n : Nat} (M : Machine n) (c : FiniteConfig (2*n)) (a b : Nat) :
    finiteStep (OrdinaryEncoding.table M) {c with choices := a} =
      (finiteStep (OrdinaryEncoding.table M) {c with choices := b}).map
        (fun t => {t with choices := a/2}) := by
  have hf : OrdinaryEncoding.table M c.state (c.physical.tape c.physical.head) (a.testBit 0) =
      OrdinaryEncoding.table M c.state (c.physical.tape c.physical.head) (b.testBit 0) := rfl
  simp only [finiteStep,hf]
  cases (OrdinaryEncoding.table M c.state (c.physical.tape c.physical.head) (b.testBit 0)).next <;> rfl

/-- All choice streams have the same finite live state and entire tape, or
all halt at the same clock, for a deterministic ordinary verifier. -/
theorem ordinary_run_choices {n : Nat} (M : Machine n) (clock : Nat)
    (c : FiniteConfig (2*n)) (a b : Nat) :
    (finiteRun (OrdinaryEncoding.table M) clock {c with choices := a}).map (fun t => (t.state,t.physical)) =
      (finiteRun (OrdinaryEncoding.table M) clock {c with choices := b}).map (fun t => (t.state,t.physical)) := by
  induction clock generalizing c a b with
  | zero => rfl
  | succ clock ih =>
    have hs := ordinary_step_choices M c a b
    cases hb : finiteStep (OrdinaryEncoding.table M) {c with choices := b} with
    | none =>
      simp only [hb,Option.map_none] at hs
      simp [finiteRun,hs,hb]
    | some next =>
      simp only [hb,Option.map_some] at hs
      have hnext : next.choices = b/2 := by
        simp only [finiteStep] at hb
        cases he : (OrdinaryEncoding.table M c.state (c.physical.tape c.physical.head) (b.testBit 0)).next with
        | none =>
          simp only [he,Option.map_none] at hb
          cases hb
        | some q =>
          simp only [he,Option.map_some,Option.some.injEq] at hb
          cases hb
          rfl
      simp only [finiteRun,hs,hb]
      have hi := ih next (a/2) (b/2)
      have heq : {next with choices := b/2} = next := by cases next; simp_all
      rw [heq] at hi
      exact hi

/-- The exact-clock finite relative verifier halts iff the original finite
Boolean program has returned true, including malformed rows and timeouts. -/
theorem verifier_halt_iff_bounded_true (p : Program) (word : List Bool) (clock choices : Nat) :
    finiteRun (relativeTable p) clock (finiteInitial (states_positive p) (value word) choices) = none ↔
      bounded p word clock = some true := by
  let c := finiteInitial (states_positive p) (value word) 0
  have hc := ordinary_run_choices (FiniteProgramAdapter.machine p) clock c choices 0
  change (finiteRun (relativeTable p) clock (finiteInitial (states_positive p) (value word) choices)).map
      (fun t => (t.state,t.physical)) =
    (finiteRun (relativeTable p) clock (finiteInitial (states_positive p) (value word) 0)).map
      (fun t => (t.state,t.physical)) at hc
  have hchoice : finiteRun (relativeTable p) clock (finiteInitial (states_positive p) (value word) choices) = none ↔
      finiteRun (relativeTable p) clock (finiteInitial (states_positive p) (value word) 0) = none := by
    cases h1 : finiteRun (relativeTable p) clock (finiteInitial (states_positive p) (value word) choices) <;>
      cases h2 : finiteRun (relativeTable p) clock (finiteInitial (states_positive p) (value word) 0) <;>
      simp_all
  rw [hchoice]
  have hstart : (FiniteProgramAdapter.machine p).start.val = 0 := rfl
  rw [show finiteInitial (states_positive p) (value word) 0 =
      lift ((loaded (FiniteProgramAdapter.machine p) (value word)).initial) false from
    initial_eq (FiniteProgramAdapter.machine p) hstart (value word)]
  change finiteRun (OrdinaryEncoding.table (FiniteProgramAdapter.machine p)) clock
      (lift ((loaded (FiniteProgramAdapter.machine p) (value word)).initial) false) = none ↔ _
  rw [finiteRun_iff_event]
  exact (bounded_true_iff_event p word clock).symm

/-- Exact source-reference behavior for any actual finite Boolean program.
The public input is hardwired; the verifier sees the complete raw tape
`publicBits ++ witness`. Invalid execution and timeout do not count as true. -/
theorem reference_iff_bounded_verifier (p : Program) (publicBits : List Bool) (count padding : Nat) :
    let k := publicBits.length+count
    let n := states p
    let g := HardwireChoiceLoader.table k n (states_positive p) publicBits.length (value publicBits) (relativeTable p)
    let total := ChoiceLoader.offset k+n
    let remaining := UnaryReferenceTail.tableWidth total g+padding
    let clock := remaining+ChoiceLoader.offset k
    referenceLanguage (canonical (bits clock (finiteProgram total g))) = true ↔
      ∃ witness : List Bool, witness.length ≤ count ∧
        bounded p (publicBits++witness) remaining = some true := by
  dsimp only
  have h := reference_hardwired_list_search publicBits count (states p) (states_positive p)
    (relativeTable p) padding
  dsimp only at h
  have he : UnaryReferenceTail.tableWidth (ChoiceLoader.offset (publicBits.length+count)+states p)
      (HardwireChoiceLoader.table (publicBits.length+count) (states p) (states_positive p)
        publicBits.length (value publicBits) (relativeTable p)) +
      (ChoiceLoader.offset (publicBits.length+count)+padding) =
      (UnaryReferenceTail.tableWidth (ChoiceLoader.offset (publicBits.length+count)+states p)
        (HardwireChoiceLoader.table (publicBits.length+count) (states p) (states_positive p)
          publicBits.length (value publicBits) (relativeTable p))+padding) +
        ChoiceLoader.offset (publicBits.length+count) := by omega
  rw [he] at h
  rw [h]
  constructor
  · rintro ⟨witness,hw,tail,haccept⟩
    exact ⟨witness,hw,(verifier_halt_iff_bounded_true p (publicBits++witness) _ tail).1 haccept⟩
  · rintro ⟨witness,hw,haccept⟩
    exact ⟨witness,hw,0,(verifier_halt_iff_bounded_true p (publicBits++witness) _ 0).2 haccept⟩

/-- A returned Boolean remains returned at every later finite clock. -/
theorem bounded_result_extend (p : Program) (word : List Bool) (small large : Nat)
    (hclock : small ≤ large) (result : Bool) (h : bounded p word small = some result) :
    bounded p word large = some result := by
  obtain ⟨t,ht,hr⟩ := (bounded_iff_result p word small result).1 h
  exact (bounded_iff_result p word large result).2 ⟨t,by omega,hr⟩

/-- Once a program has returned a Boolean, enlarging the clock cannot change
its true-result predicate. The explicit premise excludes timeout. -/
theorem bounded_true_iff_of_total (p : Program) (word : List Bool) (small large : Nat)
    (hclock : small ≤ large) (htotal : ∃ b, bounded p word small = some b) :
    (bounded p word large = some true ↔ bounded p word small = some true) := by
  constructor
  · intro hlarge
    obtain ⟨b,hsmall⟩ := htotal
    have he := bounded_unique p word small large b true hsmall hlarge
    simpa [he] using hsmall
  · exact bounded_result_extend p word small large hclock true

/-- Under an explicit totality bound, the source's longer remaining clock may
be replaced by the verifier's original bound. No timeout is silently accepted. -/
theorem reference_iff_total_verifier (p : Program) (publicBits : List Bool) (count padding budget : Nat)
    (hclock : budget ≤ UnaryReferenceTail.tableWidth
      (ChoiceLoader.offset (publicBits.length+count)+states p)
      (HardwireChoiceLoader.table (publicBits.length+count) (states p) (states_positive p)
        publicBits.length (value publicBits) (relativeTable p)) + padding)
    (htotal : ∀ witness : List Bool, witness.length ≤ count →
      ∃ result, bounded p (publicBits++witness) budget = some result) :
    let k := publicBits.length+count
    let n := states p
    let g := HardwireChoiceLoader.table k n (states_positive p) publicBits.length (value publicBits) (relativeTable p)
    let total := ChoiceLoader.offset k+n
    let remaining := UnaryReferenceTail.tableWidth total g+padding
    let clock := remaining+ChoiceLoader.offset k
    referenceLanguage (canonical (bits clock (finiteProgram total g))) = true ↔
      ∃ witness : List Bool, witness.length ≤ count ∧ bounded p (publicBits++witness) budget = some true := by
  dsimp only
  have h := reference_iff_bounded_verifier p publicBits count padding
  dsimp only at h
  rw [h]
  constructor
  · rintro ⟨witness,hw,htrue⟩
    exact ⟨witness,hw,(bounded_true_iff_of_total p (publicBits++witness) budget _ hclock (htotal witness hw)).1 htrue⟩
  · rintro ⟨witness,hw,htrue⟩
    exact ⟨witness,hw,(bounded_true_iff_of_total p (publicBits++witness) budget _ hclock (htotal witness hw)).2 htrue⟩

/-- The bound itself is enough padding: no assumption about P = NP, and no
separate inequality about the input-dependent table width, is needed. -/
def verifierReferenceFrame (p : Program) (publicBits : List Bool) (count budget : Nat) : List Bool :=
  let k := publicBits.length+count
  let n := states p
  let g := HardwireChoiceLoader.table k n (states_positive p) publicBits.length (value publicBits) (relativeTable p)
  let total := ChoiceLoader.offset k+n
  let remaining := UnaryReferenceTail.tableWidth total g+budget
  let clock := remaining+ChoiceLoader.offset k
  canonical (bits clock (finiteProgram total g))

/-- One uniform finite program and one finite budget work for all witnesses;
padding by that budget supplies adequate source time without extending a
timed-out computation. -/
theorem reference_padded_total_verifier (p : Program) (publicBits : List Bool) (count budget : Nat)
    (htotal : ∀ witness : List Bool, witness.length ≤ count →
      ∃ result, bounded p (publicBits++witness) budget = some result) :
    referenceLanguage (verifierReferenceFrame p publicBits count budget) = true ↔
      ∃ witness : List Bool, witness.length ≤ count ∧ bounded p (publicBits++witness) budget = some true := by
  have h := reference_iff_total_verifier p publicBits count budget budget (by omega) htotal
  simpa only [verifierReferenceFrame] using h

/-- The reference frame for the fixed finite verifier has an explicit
quadratic state-count size bound, plus the supplied verifier budget. -/
theorem verifierReferenceFrame_length (p : Program) (publicBits : List Bool) (count budget : Nat) :
    let k := publicBits.length+count
    let s := ChoiceLoader.offset k+states p
    (verifierReferenceFrame p publicBits count budget).length ≤
      2*((4*s)*(16*s+8)+(ChoiceLoader.offset k+budget))+1 := by
  dsimp only
  have h := reference_hardwired_frame_bound publicBits count (states p) (states_positive p) (relativeTable p) budget
  dsimp only at h
  have he : UnaryReferenceTail.tableWidth (ChoiceLoader.offset (publicBits.length+count)+states p)
      (HardwireChoiceLoader.table (publicBits.length+count) (states p) (states_positive p)
        publicBits.length (value publicBits) (relativeTable p)) +
      (ChoiceLoader.offset (publicBits.length+count)+budget) =
      (UnaryReferenceTail.tableWidth (ChoiceLoader.offset (publicBits.length+count)+states p)
        (HardwireChoiceLoader.table (publicBits.length+count) (states p) (states_positive p)
          publicBits.length (value publicBits) (relativeTable p))+budget) +
        ChoiceLoader.offset (publicBits.length+count) := by omega
  rw [he] at h
  simpa only [verifierReferenceFrame] using h

end Shared.PNP.Record285.HardwireFiniteVerifier
