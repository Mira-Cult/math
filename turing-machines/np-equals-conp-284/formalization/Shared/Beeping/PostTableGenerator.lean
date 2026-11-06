import Shared.Beeping.PostTableBinding

/-! An executable finite-table generator given executable finite-state
numbering and row functions. The proofs require totality and closure on the
represented states. Obtaining such a numbering for the comparator remains a
separate obligation. -/
namespace Shared.Beeping.PostTableGenerator
open Turing
open Shared.Beeping.ComparisonSingleTape Shared.Beeping.ComparisonAlphabetBits
open Shared.Beeping.BinaryBlockScan Shared.Beeping.BinaryBlockWrite
open Shared.Beeping.BinarySourceCompiler Shared.Beeping.PostTableBinding

variable {Λ : Type} [Inhabited Λ]

/-- The supplied indexing functions are data. `total` and `closed` are proof
obligations, not runtime decisions about arbitrary machine behavior. -/
structure FiniteIndex (M : TM0.Machine Alphabet Λ) (m : Nat) where
  state : Fin m → Λ
  index : Λ → Fin m
  total : ∀ q a, ∃ dst op, M (state q) a = some (dst,op)
  closed : ∀ q a dst op, M (state q) a = some (dst,op) → state (index dst) = dst

/-- Compute a reverse index by scanning a supplied finite list. Unlisted
states map to the supplied fallback; closure proves this fallback is not used
for the generated rows. -/
def listingIndex [BEq Λ] {m : Nat} (states : Vector Λ m) (fallback : Fin m) (x : Λ) : Fin m :=
  let i := states.toList.idxOf x
  if h : i < m then ⟨i,h⟩ else fallback

theorem listingIndex_correct [BEq Λ] [LawfulBEq Λ] {m : Nat} (states : Vector Λ m)
    (fallback : Fin m) (x : Λ) (h : x ∈ states.toList) :
    states.get (listingIndex states fallback x) = x := by
  have hi : states.toList.idxOf x < m := by
    simpa using List.idxOf_lt_length_of_mem h
  unfold listingIndex
  rw [dif_pos hi]
  change states[states.toList.idxOf x] = x
  rw [← Vector.getElem_toList (by simpa using hi)]
  exact List.getElem_idxOf (by simpa using hi)

/-- A literal finite state listing plus totality and closure supplies the
numbering using the executable reverse lookup. Duplicates are harmless. -/
def fromListing [BEq Λ] [LawfulBEq Λ] {m : Nat} (M : TM0.Machine Alphabet Λ)
    (states : Vector Λ m) (fallback : Fin m)
    (total : ∀ q a, ∃ dst op, M (states.get q) a = some (dst,op))
    (closed : ∀ q a dst op, M (states.get q) a = some (dst,op) → dst ∈ states.toList) :
    FiniteIndex M m where
  state := states.get
  index := listingIndex states fallback
  total := total
  closed := by intro q a dst op h; exact listingIndex_correct states fallback dst (closed q a dst op h)

def action : TM0.Stmt Alphabet → Action
  | .write a => .write a
  | .move .left => .left
  | .move .right => .right

theorem statement_action (op : TM0.Stmt Alphabet) : statement (action op) = op := by
  cases op with
  | write a => rfl
  | move d => cases d <;> rfl

/-- Valid 13-bit words decode to alphabet symbols; malformed words use a
fixed fallback row. -/
def decodedWord (w : Fin 8192) : Option Alphabet := decode (unpath 13 (8192+w.val))

theorem decoded_wordOf (a : Alphabet) : decodedWord (wordOf a) = some a := by
  simp [decodedWord,wordOf_decode,decode_encode]

def generateRow {m : Nat} (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (numbering : FiniteIndex M m) (q : Fin m) (w : Fin 8192) : SourceRow m :=
  match decodedWord w with
  | none => ⟨q,.write default,false⟩
  | some a => match M (numbering.state q) a with
    | none => ⟨q,.write default,false⟩
    | some (dst,op) => ⟨numbering.index dst,action op,flags (numbering.state q) a⟩

theorem malformed_fallback {m : Nat} (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (numbering : FiniteIndex M m) (q : Fin m) (w : Fin 8192) (h : decodedWord w = none) :
    generateRow M flags numbering q w = ⟨q,.write default,false⟩ := by
  simp [generateRow,h]

/-- The generator visits the finite table entries; it is executable when its
supplied machine, flag and numbering functions are executable. -/
def generate {m : Nat} (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (numbering : FiniteIndex M m) : SourceTable m :=
  Vector.ofFn fun q => Vector.ofFn fun w => generateRow M flags numbering q w

theorem selected_generate {m : Nat} (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (numbering : FiniteIndex M m) (q : Fin m) (a : Alphabet) :
    selected (generate M flags numbering) q a = generateRow M flags numbering q (wordOf a) := by
  change ((Vector.ofFn (fun q : Fin m => Vector.ofFn (fun w : Fin 8192 =>
    generateRow M flags numbering q w)))[q.val]).get (wordOf a) = _
  rw [Vector.getElem_ofFn]
  change (Vector.ofFn (fun w : Fin 8192 => generateRow M flags numbering q w))[(wordOf a).val] = _
  rw [Vector.getElem_ofFn]

set_option maxRecDepth 32768 in
theorem generateRow_valid {m : Nat} (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (numbering : FiniteIndex M m) (q : Fin m) (a : Alphabet) (dst : Λ) (op : TM0.Stmt Alphabet)
    (h : M (numbering.state q) a = some (dst,op)) :
    generateRow M flags numbering q (wordOf a) =
      ⟨numbering.index dst,action op,flags (numbering.state q) a⟩ := by
  simp only [generateRow,decoded_wordOf]
  rw [h]

/-- The generated literal table discharges both row and event matching for
all represented states and valid source alphabet symbols. -/
def binding {m : Nat} (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (numbering : FiniteIndex M m) : Binding M flags (generate M flags numbering) where
  state := numbering.state
  row := by
    intro q a
    obtain ⟨dst,op,hm⟩ := numbering.total q a
    have hc := numbering.closed q a dst op hm
    rw [selected_generate,generateRow_valid M flags numbering q a dst op hm]
    simp only [statement_action,hc]
    exact hm
  event := by
    intro q a
    obtain ⟨dst,op,hm⟩ := numbering.total q a
    rw [selected_generate,generateRow_valid M flags numbering q a dst op hm]

/-- With the explicit numbering obligations supplied, the generated table
inherits the post-Turing-to-binary infinite-run refinement. -/
theorem eventuallySilent_iff {m : Nat} (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (numbering : FiniteIndex M m) (start : Fin m) (initial : PostSourceRefinement.PostConfig m) :
    (BinarySourceLoaded.binaryFrom (generate M flags numbering) start (PostSourceRefinement.sourceInitial initial)).EventuallySilent ↔
      (externalSystem M flags ⟨numbering.state initial.state,initial.tape⟩).EventuallySilent :=
  PostTableBinding.eventuallySilent_iff (binding M flags numbering) start initial

theorem infinitelyManyBeeps_iff {m : Nat} (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (numbering : FiniteIndex M m) (start : Fin m) (initial : PostSourceRefinement.PostConfig m) :
    (BinarySourceLoaded.binaryFrom (generate M flags numbering) start (PostSourceRefinement.sourceInitial initial)).InfinitelyManyBeeps ↔
      (externalSystem M flags ⟨numbering.state initial.state,initial.tape⟩).InfinitelyManyBeeps :=
  PostTableBinding.infinitelyManyBeeps_iff (binding M flags numbering) start initial

end Shared.Beeping.PostTableGenerator
