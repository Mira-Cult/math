import Shared.Beeping.PostInputLoader
import Shared.Beeping.RefinementEventCount

/-! Event occurrence and uniqueness through the blank-start loader and
post-Turing compiler. -/
namespace Shared.Beeping.PostInputEvents
open Turing
open Shared.Beeping.Machines Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.BinarySourceCompiler Shared.Beeping.PostInputLoader

namespace BinaryLoader

theorem hasBeep_iff {n : Nat} (M : Machine n) (bits : List Bool) :
    (Shared.Beeping.BinaryLoader.machine M bits).system.HasBeep ↔
      (Shared.Beeping.BinaryLoader.loadedSystem M bits).HasBeep := by
  constructor
  · rintro ⟨t,ht⟩
    have hb := Shared.Beeping.BinaryLoader.boot_silent M bits
    have hle : 2 * Shared.Beeping.BinaryLoader.count M.blank bits ≤ t := by
      by_contra h
      exact hb t (by omega) ht
    refine ⟨t - 2 * Shared.Beeping.BinaryLoader.count M.blank bits, ?_⟩
    apply (Shared.Beeping.BinaryLoader.event_shift M bits _).1
    convert ht using 1 <;> omega
  · rintro ⟨t,ht⟩
    exact ⟨2 * Shared.Beeping.BinaryLoader.count M.blank bits + t,
      (Shared.Beeping.BinaryLoader.event_shift M bits t).2 ht⟩

theorem atMostOneBeep_iff {n : Nat} (M : Machine n) (bits : List Bool) :
    (Shared.Beeping.BinaryLoader.machine M bits).system.AtMostOneBeep ↔
      (Shared.Beeping.BinaryLoader.loadedSystem M bits).AtMostOneBeep := by
  constructor
  · intro h t u ht hu
    have he := h _ _ ((Shared.Beeping.BinaryLoader.event_shift M bits t).2 ht)
      ((Shared.Beeping.BinaryLoader.event_shift M bits u).2 hu)
    omega
  · intro h t u ht hu
    have hb := Shared.Beeping.BinaryLoader.boot_silent M bits
    have ht' : 2 * Shared.Beeping.BinaryLoader.count M.blank bits ≤ t := by
      by_contra hn
      exact hb t (by omega) ht
    have hu' : 2 * Shared.Beeping.BinaryLoader.count M.blank bits ≤ u := by
      by_contra hn
      exact hb u (by omega) hu
    have ht'' : (Shared.Beeping.BinaryLoader.loadedSystem M bits).BeepAt
        (t - 2 * Shared.Beeping.BinaryLoader.count M.blank bits) := by
      apply (Shared.Beeping.BinaryLoader.event_shift M bits _).1
      convert ht using 1 <;> omega
    have hu'' : (Shared.Beeping.BinaryLoader.loadedSystem M bits).BeepAt
        (u - 2 * Shared.Beeping.BinaryLoader.count M.blank bits) := by
      apply (Shared.Beeping.BinaryLoader.event_shift M bits _).1
      convert hu using 1 <;> omega
    have he := h _ _ ht'' hu''
    omega
end BinaryLoader

variable {Λ : Type} [Inhabited Λ]

/-- The loader and compiler preserve occurrence and uniqueness, in addition
to the previously proved eventual-silence and infinite-beeping equivalences. -/
theorem bound_events {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : PostTableBinding.Binding M flags tab) (start : Fin m) (input : List Alphabet) :
    let target := (Shared.Beeping.BinaryLoader.machine (BinarySourceCompiler.machine tab start)
      (payload input)).system
    let source := PostTableBinding.externalSystem M flags ⟨binding.state start,Tape.mk₁ input⟩
    (target.HasBeep ↔ source.HasBeep) ∧ (target.AtMostOneBeep ↔ source.AtMostOneBeep) := by
  let p : PostSourceRefinement.PostConfig m := ⟨start,Tape.mk₁ input⟩
  have he : Shared.Beeping.BinaryLoader.loadedSystem (BinarySourceCompiler.machine tab start) (payload input) =
      BinarySourceLoaded.binaryFrom tab start (PostSourceRefinement.sourceInitial p) := by
    change EventSystem.mk (Shared.Beeping.BinaryLoader.loaded (BinarySourceCompiler.machine tab start) (payload input)) _ = _
    rw [compiler_loaded]
    rfl
  have hr := PostTableBinding.binaryRefinement binding start p
  constructor
  · rw [BinaryLoader.hasBeep_iff,he]
    exact hr.hasBeep_iff.symm
  · rw [BinaryLoader.atMostOneBeep_iff,he]
    exact hr.atMostOneBeep_iff.symm

end Shared.Beeping.PostInputEvents
