import Shared.Beeping.BinaryLoader
import Shared.Beeping.PostSourceRefinement
import Shared.Beeping.PostTableBinding

/-! A finite payload for a standard mathlib post-Turing input tape. This loads
one fixed input list; it does not implement the rejection controller or create
an executable finite listing of a comparator's source states. -/
namespace Shared.Beeping.PostInputLoader
open Turing
open Shared.Beeping.Machines
open Shared.Beeping.ComparisonAlphabetBits Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.BinarySourceCompiler Shared.Beeping.BinarySourceRefinement
open Shared.Beeping.BinaryLoader

/-- Standard post-Turing list input has blank cells outside its finite range. -/
theorem postTape_blank (input : List Alphabet) (i : Int)
    (h : i < 0 ∨ (input.length : Int) ≤ i) : (Tape.mk₁ input).nth i = default := by
  cases i with
  | ofNat j =>
    simp only [Int.ofNat_eq_natCast] at h ⊢
    have hj : input.length ≤ j := by omega
    change (Tape.mk' (ListBlank.mk []) (ListBlank.mk input)).nth j = default
    rw [Tape.mk'_nth_nat,ListBlank.nth_mk,List.getI_eq_getElem?_getD]
    simp [List.getElem?_eq_none hj]
  | negSucc j =>
    simp [Tape.mk₁,Tape.mk₂,Tape.mk',Tape.nth,ListBlank.nth_mk]

/-- A bit outside the finite encoded input interval is blank. -/
theorem binary_postTape_blank (input : List Alphabet) (i : Int)
    (h : i < 0 ∨ (13*input.length : Nat) ≤ i) :
    binaryTape (Tape.mk₁ input).nth i = false := by
  have hs : (Tape.mk₁ input).nth (i/13) = default := by
    apply postTape_blank
    omega
  unfold binaryTape
  rw [hs,encode_blank]
  simp only [List.getElem?_replicate]
  split <;> rfl

/-- The finite payload is the exact encoded tape interval, computed from the
actual post-Turing tape; no answer bits are added. -/
def payload (input : List Alphabet) : List Bool :=
  (List.range (13*input.length)).map (fun i : Nat => binaryTape (Tape.mk₁ input).nth i)

theorem payload_length (input : List Alphabet) : (payload input).length = 13*input.length := by
  simp [payload]

/-- The bootstrap's state and transition count, including empty input. -/
theorem bootstrap_count (input : List Alphabet) :
    2 * BinaryLoader.count false (payload input) = 2 * max (13 * input.length) 1 := by
  rw [BinaryLoader.count_eq_max,payload_length]

/-- The generic blank-start loader produces the whole encoded post-Turing
tape, including blank cells to its left and beyond the finite input. -/
theorem loaded_tape {n : Nat} (M : Machine n) (input : List Alphabet)
    (hblank : M.blank = false) (hhead : M.startHead = 0) :
    (loaded M (payload input)).tape = binaryTape (Tape.mk₁ input).nth := by
  funext i
  cases i with
  | ofNat j =>
    simp only [Int.ofNat_eq_natCast]
    by_cases hj : j < 13*input.length
    · have h := loaded_at M (payload input) j
      simp only [hhead,Int.zero_add] at h
      rw [h]
      simp [payload,List.getElem_range,hj,hblank]
    · have ho : (input.length : Int)*13 ≤ (j : Int) := by omega
      have hb := binary_postTape_blank input (j : Int) (Or.inr (by omega))
      have hl := loaded_outside M (payload input) (j : Int) (Or.inr (by rw [hhead,payload_length]; omega))
      rw [hl,hb,hblank]
  | negSucc j =>
    have hb := binary_postTape_blank input (Int.negSucc j) (Or.inl (by omega))
    have hl := loaded_outside M (payload input) (Int.negSucc j) (Or.inl (by rw [hhead]; omega))
    rw [hl,hb,hblank]

/-- A fixed finite post-Turing input list is loaded from blank tape into the
binary compiler's exact initial configuration. -/
theorem compiler_loaded {m : Nat} (tab : SourceTable m) (start : Fin m) (input : List Alphabet) :
    loaded (BinarySourceCompiler.machine tab start) (payload input) =
      begin start (binaryTape (Tape.mk₁ input).nth) 0 := by
  have ht := loaded_tape (BinarySourceCompiler.machine tab start) input rfl rfl
  simp only [loaded, BinarySourceCompiler.machine, begin, scanConfig, BinaryBlockScan.begin, ready]
  congr 1

/-- From an entirely blank binary tape, load the finite post-Turing input and
then simulate the table with exactly the same eventual-silence behavior. -/
theorem blankStart_eventuallySilent_iff {m : Nat} (tab : SourceTable m)
    (start : Fin m) (input : List Alphabet) :
    (BinaryLoader.machine (BinarySourceCompiler.machine tab start) (payload input)).system.EventuallySilent ↔
      (PostSourceRefinement.postSystem tab ⟨start,Tape.mk₁ input⟩).EventuallySilent := by
  let p : PostSourceRefinement.PostConfig m := ⟨start,Tape.mk₁ input⟩
  have hl : loaded (BinarySourceCompiler.machine tab start) (payload input) =
      begin (PostSourceRefinement.sourceInitial p).state
        (binaryTape (PostSourceRefinement.sourceInitial p).tape)
        (13*(PostSourceRefinement.sourceInitial p).head) := by
    simpa [p,PostSourceRefinement.sourceInitial] using compiler_loaded tab start input
  exact (BinaryLoader.compiled_eventuallySilent_iff tab start
    (PostSourceRefinement.sourceInitial p) (payload input) hl).trans
      (PostSourceRefinement.simulation tab p).toEventRefinement.eventuallySilent_iff.symm

/-- A checked binding transfers the blank-start result to the external
post-Turing machine. The binding still has to be constructed for the program. -/
theorem bound_blankStart_eventuallySilent_iff {Λ : Type} [Inhabited Λ]
    {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : PostTableBinding.Binding M flags tab) (start : Fin m) (input : List Alphabet) :
    (BinaryLoader.machine (BinarySourceCompiler.machine tab start) (payload input)).system.EventuallySilent ↔
      (PostTableBinding.externalSystem M flags ⟨binding.state start,Tape.mk₁ input⟩).EventuallySilent := by
  exact (blankStart_eventuallySilent_iff tab start input).trans
    (PostTableBinding.simulation binding ⟨start,Tape.mk₁ input⟩).toEventRefinement.eventuallySilent_iff.symm

theorem bound_blankStart_infinitelyManyBeeps_iff {Λ : Type} [Inhabited Λ]
    {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : PostTableBinding.Binding M flags tab) (start : Fin m) (input : List Alphabet) :
    (BinaryLoader.machine (BinarySourceCompiler.machine tab start) (payload input)).system.InfinitelyManyBeeps ↔
      (PostTableBinding.externalSystem M flags ⟨binding.state start,Tape.mk₁ input⟩).InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    ← EventSystem.not_eventuallySilent_iff_infinitelyMany]
  exact not_congr (bound_blankStart_eventuallySilent_iff binding start input)

namespace Fixtures
example : payload [] = [] := by rfl
example : (payload [default]).length = 13 := by simp [payload_length]
end Fixtures

end Shared.Beeping.PostInputLoader
