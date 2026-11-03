import Shared.ComplexityBridge.TM0FiniteProgram

/-! Classically number a finite supported binary post-Turing control, with
its initial state at zero. This is an existence bridge: it does not claim
executable reification of arbitrary Lean transition functions. -/
namespace Shared.ComplexityBridge.TM0FiniteReindex
open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program (runSteps_front)
open Shared.Codes.FinitePrograms

variable {Λ : Type} [Inhabited Λ]
variable (M : TM0.Machine Bool Λ) (S : Finset Λ) (hs : TM0.Supports M (S : Set Λ))

def zero : Fin S.card := ⟨0, Finset.card_pos.mpr ⟨default,hs.1⟩⟩

noncomputable def baseEquiv : {q : Λ // q ∈ S} ≃ Fin S.card := by
  classical
  simpa using Fintype.equivFin {q : Λ // q ∈ S}

/-- Place the source machine's default state at numeric state zero. -/
noncomputable def numbering : {q : Λ // q ∈ S} ≃ Fin S.card := by
  classical
  exact (baseEquiv S).trans (Equiv.swap (baseEquiv S ⟨default,hs.1⟩) (zero M S hs))

noncomputable def state (i : Fin S.card) : Λ := ((numbering M S hs).symm i).val
noncomputable def index (q : Λ) : Fin S.card := by
  classical
  exact if h : q ∈ S then numbering M S hs ⟨q,h⟩ else zero M S hs

theorem state_in_support (i : Fin S.card) : state M S hs i ∈ S :=
  ((numbering M S hs).symm i).property

theorem state_index (q : Λ) (hq : q ∈ S) : state M S hs (index M S hs q) = q := by
  classical
  simp [index,hq,state]

theorem index_default : index M S hs default = zero M S hs := by
  classical
  simp [index,hs.1,numbering]

theorem index_state (i : Fin S.card) : index M S hs (state M S hs i) = i := by
  classical
  simp [index,state,state_in_support]

/-- The table is finite; rows obtained from unsupported states have a fixed
fallback, which the simulation never uses on a supported source run. -/
noncomputable def machine : TM0FiniteProgram.Machine S.card := fun i b =>
  (M (state M S hs i) b).map fun row => (index M S hs row.1,row.2)

theorem machine_row (q : Λ) (hq : q ∈ S) (b : Bool) :
    machine M S hs (index M S hs q) b =
      (M q b).map (fun row => (index M S hs row.1,row.2)) := by
  simp [machine,state_index M S hs q hq]

noncomputable def config (c : TM0.Cfg Bool Λ) : TM0.Cfg Bool (Fin S.card) :=
  ⟨index M S hs c.q,c.Tape⟩

theorem step_map (c : TM0.Cfg Bool Λ) (h : c.q ∈ S) :
    letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
    TM0.step (machine M S hs) (config M S hs c) =
      (TM0.step M c).map (config M S hs) := by
  letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
  rcases c with ⟨q,T⟩
  simp only [config,TM0.step,machine_row M S hs q h]
  cases hrow : M q T.head with
  | none => rfl
  | some row => rcases row with ⟨dst,op⟩; cases op <;> rfl

/-- Reindexing preserves every successful finite source run and its entire
tape, including the final halt configuration. -/
theorem run_map (n : Nat) (c c' : TM0.Cfg Bool Λ) (hmem : c.q ∈ S)
    (hrun : runSteps (TM0.step M) n c = some c') :
    letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
    runSteps (TM0.step (machine M S hs)) n (config M S hs c) = some (config M S hs c') ∧ c'.q ∈ S := by
  letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
  induction n generalizing c with
  | zero =>
    change some c = some c' at hrun
    cases Option.some.inj hrun
    exact ⟨rfl,hmem⟩
  | succ n ih =>
    rw [runSteps_front] at hrun
    cases hstep : TM0.step M c with
    | none => rw [hstep] at hrun; contradiction
    | some mid =>
      rw [hstep] at hrun
      have hnext : mid.q ∈ S := TM0.step_supports M hs (by rw [hstep]; rfl) hmem
      obtain ⟨hr,hfinal⟩ := ih mid hnext hrun
      constructor
      · rw [runSteps_front,step_map M S hs c hmem,hstep]
        exact hr
      · exact hfinal

theorem initial_config (input : List Bool) :
    letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
    config M S hs (TM0.init input) = TM0.init input := by
  letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
  simp [config,TM0.init,index_default]

theorem halt_row (c : TM0.Cfg Bool Λ) (hmem : c.q ∈ S)
    (hhalt : TM0.step M c = none) :
    machine M S hs (index M S hs c.q) c.Tape.head = none := by
  rw [machine_row M S hs c.q hmem]
  cases hrow : M c.q c.Tape.head with
  | none => rfl
  | some row =>
    cases c with
    | mk q T =>
      change (M q T.head).map _ = none at hhalt
      rw [hrow] at hhalt
      contradiction

include S hs

/-- A single valid finite table simulates all supported halted source runs,
returning the final head bit in at most `2*n+1` steps. -/
theorem finite_program :
    ∃ p : Program, valid p = true ∧
      ∀ (input : List Bool) (n : Nat) (last : TM0.Cfg Bool Λ),
        runSteps (TM0.step M) n (TM0.init input) = some last →
        TM0.step M last = none → bounded p input (2*n+1) = some last.Tape.head := by
  letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
  refine ⟨TM0FiniteProgram.program (machine M S hs),TM0FiniteProgram.program_valid _,?_⟩
  intro input n last hrun hhalt
  have hinit : (TM0.init input : TM0.Cfg Bool Λ).q ∈ S := hs.1
  obtain ⟨hr,hl⟩ := run_map M S hs n (TM0.init input) last hinit hrun
  rw [initial_config M S hs input] at hr
  have hh := halt_row M S hs last hl hhalt
  have hdefault : (default : Fin S.card).val = 0 := rfl
  exact TM0FiniteProgram.bounded_from_source_run (machine M S hs) input n
    (index M S hs last.q) last.Tape hdefault hr hh

end Shared.ComplexityBridge.TM0FiniteReindex
