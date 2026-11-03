import Shared.Beeping.PostTableGenerator
import Shared.Beeping.PostInputLoader
import Shared.Beeping.ComparisonCommit
import Shared.Beeping.PostInputEvents

/-! A finite-support existence bridge. The numbering uses classical finite
choice, so this does not extract an executable listing from an arbitrary
function-valued machine. Every resulting table is nevertheless finite, and
the operational theorems apply to the table itself. -/
namespace Shared.Beeping.PostFiniteSupport
open Turing
open Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.PostTableGenerator
open Shared.Beeping.PostTableBinding
open Shared.Beeping.BinarySourceCompiler
open Shared.Beeping.PostInputLoader

variable {Λ : Type} [Inhabited Λ] [DecidableEq Λ]

noncomputable def supportEquiv (S : Finset Λ) : {q : Λ // q ∈ S} ≃ Fin S.card := by
  simpa using Fintype.equivFin {q : Λ // q ∈ S}

/-- Number the supported states. Totality and support are the only semantic
requirements. This is an existence construction, not an effective extraction. -/
noncomputable def numbering (M : TM0.Machine Alphabet Λ) (S : Finset Λ)
    (hS : TM0.Supports M (S : Set Λ))
    (htotal : ∀ q ∈ S, ∀ a, ∃ dst op, M q a = some (dst,op)) :
    FiniteIndex M S.card where
  state := fun i => ((supportEquiv S).symm i).val
  index := fun q => supportEquiv S (if h : q ∈ S then ⟨q,h⟩ else ⟨default,hS.1⟩)
  total := by
    intro q a
    exact htotal _ ((supportEquiv S).symm q).property a
  closed := by
    intro q a dst op h
    have hd : dst ∈ S := hS.2 (by rw [h]; rfl) ((supportEquiv S).symm q).property
    simp only [dif_pos hd, Equiv.symm_apply_apply]

noncomputable def start (S : Finset Λ) (q : Λ) (hq : q ∈ S) : Fin S.card :=
  supportEquiv S ⟨q,hq⟩

theorem start_state (M : TM0.Machine Alphabet Λ) (S : Finset Λ)
    (hS : TM0.Supports M (S : Set Λ))
    (htotal : ∀ q ∈ S, ∀ a, ∃ dst op, M q a = some (dst,op))
    (q : Λ) (hq : q ∈ S) :
    (numbering M S hS htotal).state (start S q hq) = q := by
  simp [numbering,start]

/-- A supported total post-Turing table admits a finite generated table whose
blank-start binary execution has exactly its eventual-silence behavior. -/
theorem blankStart_of_support (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))
    (htotal : ∀ q ∈ S, ∀ a, ∃ dst op, M q a = some (dst,op))
    (q : Λ) (hq : q ∈ S) (input : List Alphabet) :
    let idx := numbering M S hS htotal
    let tab := generate M flags idx
    (Shared.Beeping.BinaryLoader.machine
      (BinarySourceCompiler.machine tab (start S q hq)) (payload input)).system.EventuallySilent ↔
      (externalSystem M flags ⟨q,Tape.mk₁ input⟩).EventuallySilent := by
  dsimp only
  have h := bound_blankStart_eventuallySilent_iff
    (binding M flags (numbering M S hS htotal)) (start S q hq) input
  change _ ↔ (externalSystem M flags
    ⟨(numbering M S hS htotal).state (start S q hq),Tape.mk₁ input⟩).EventuallySilent at h
  rw [start_state] at h
  exact h

theorem blankStart_events_of_support (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))
    (htotal : ∀ q ∈ S, ∀ a, ∃ dst op, M q a = some (dst,op))
    (q : Λ) (hq : q ∈ S) (input : List Alphabet) :
    let idx := numbering M S hS htotal
    let tab := generate M flags idx
    let target := (Shared.Beeping.BinaryLoader.machine
      (BinarySourceCompiler.machine tab (start S q hq)) (payload input)).system
    let source := externalSystem M flags ⟨q,Tape.mk₁ input⟩
    (target.HasBeep ↔ source.HasBeep) ∧ (target.AtMostOneBeep ↔ source.AtMostOneBeep) := by
  dsimp only
  have h := PostInputEvents.bound_events (binding M flags (numbering M S hS htotal))
    (start S q hq) input
  change (_ ↔ (externalSystem M flags
    ⟨(numbering M S hS htotal).state (start S q hq),Tape.mk₁ input⟩).HasBeep) ∧
    (_ ↔ (externalSystem M flags
    ⟨(numbering M S hS htotal).state (start S q hq),Tape.mk₁ input⟩).AtMostOneBeep) at h
  rw [start_state] at h
  exact h

end Shared.Beeping.PostFiniteSupport
