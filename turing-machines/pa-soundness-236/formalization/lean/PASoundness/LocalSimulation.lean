import PASoundness.Refinement

/-!
Finite local blocks for composing literal transition proofs. Zero-step blocks
are useful for pure reads and administrative identities; a complete source
step must still satisfy the separate strict positivity obligation.
-/
namespace PASoundness
namespace WordEventSystem

variable {C A : Type} (M : WordEventSystem C A)

/-- An exact finite segment, including its ordered output word. -/
structure Block (start : C) (steps : Nat) (finish : C) (word : List A) : Prop where
  endpoint : M.advance start steps = finish
  output : M.wordFrom start steps = word

theorem Block.refl (c : C) : M.Block c 0 c [] := ⟨rfl, rfl⟩

theorem Block.single {start finish : C} {word : List A}
    (h : M.step start = (finish, word)) : M.Block start 1 finish word := by
  constructor
  · change (M.step start).1 = finish
    rw [h]
  · change [] ++ (M.step start).2 = word
    rw [h]
    rfl

/-- Sequential composition adds actual transition counts and concatenates
words in execution order. No event permutation or prefix deletion is allowed. -/
theorem Block.trans {start middle finish : C} {left right : Nat}
    {first second : List A} (h₁ : M.Block start left middle first)
    (h₂ : M.Block middle right finish second) :
    M.Block start (left+right) finish (first++second) := by
  constructor
  · rw [M.advance_add, h₁.endpoint, h₂.endpoint]
  · rw [M.wordFrom_add, h₁.output, h₁.endpoint, h₂.output]

theorem Block.snoc {start middle finish : C} {steps : Nat}
    {first second : List A} (h₁ : M.Block start steps middle first)
    (h₂ : M.step middle = (finish, second)) :
    M.Block start (steps+1) finish (first++second) :=
  h₁.trans M (Block.single M h₂)

/-- Repeat an exact loop segment a finite number of times. The resulting
transition count and every copy of the ordered output are retained. -/
theorem Block.iterate {c : C} {steps : Nat} {word : List A}
    (h : M.Block c steps c word) (count : Nat) :
    M.Block c (steps*count) c (List.replicate count word).flatten := by
  induction count with
  | zero => simpa using Block.refl M c
  | succ count ih =>
    simpa [Nat.mul_succ, Nat.add_comm, List.replicate_succ] using h.trans M ih

theorem Block.positive_trans_left {start middle finish : C} {left right : Nat}
    {first second : List A} (_h₁ : M.Block start left middle first)
    (_h₂ : M.Block middle right finish second) (hp : 0 < left) : 0 < left+right := by
  omega

theorem Block.positive_trans_right {start middle finish : C} {left right : Nat}
    {first second : List A} (_h₁ : M.Block start left middle first)
    (_h₂ : M.Block middle right finish second) (hp : 0 < right) : 0 < left+right := by
  omega

/-- An emitted position has a unique value in any deterministic ordered
execution. This does not manufacture values at missing positions. -/
theorem emitsAtPosition_unique {k : Nat} {a b : A}
    (ha : M.EmitsAtPosition k a) (hb : M.EmitsAtPosition k b) : a = b := by
  obtain ⟨pre₁, len₁, t₁, tail₁, h₁⟩ := ha
  obtain ⟨pre₂, len₂, t₂, tail₂, h₂⟩ := hb
  obtain ⟨later₁, e₁⟩ := M.prefix_extends (Nat.le_max_left t₁ t₂)
  obtain ⟨later₂, e₂⟩ := M.prefix_extends (Nat.le_max_right t₁ t₂)
  have g₁ : (M.prefixWord (max t₁ t₂))[k]? = some a := by
    rw [e₁, h₁]
    simp [len₁]
  have g₂ : (M.prefixWord (max t₁ t₂))[k]? = some b := by
    rw [e₂, h₂]
    simp [len₂]
  exact Option.some.inj (g₁.symm.trans g₂)

end WordEventSystem

/-- Construct the global refinement interface from a silent local startup and
local finite blocks. Only per-step endpoint relations and exact finite words
are inputs; complete-trace equality is derived by `SegmentSimulation`. -/
def SegmentSimulation.ofBlocks {S T A : Type}
    {source : WordEventSystem S A} {target : WordEventSystem T A}
    (Rel : S → T → Prop) (startup : Nat) (initialTarget : T)
    (initialBlock : target.Block target.initial startup initialTarget [])
    (initialRelated : Rel source.initial initialTarget)
    (duration : S → T → Nat)
    (positive : ∀ s t, Rel s t → 0 < duration s t)
    (blocks : ∀ s t, Rel s t → ∃ finish,
      target.Block t (duration s t) finish (source.step s).2 ∧
        Rel (source.step s).1 finish) : SegmentSimulation source target where
  Rel := Rel
  startup := startup
  initial := by
    change Rel source.initial (target.advance target.initial startup)
    rw [initialBlock.endpoint]
    exact initialRelated
  startup_silent := initialBlock.output
  duration := duration
  positive := positive
  next := by
    intro s t h
    obtain ⟨finish, block, related⟩ := blocks s t h
    rw [block.endpoint]
    exact related
  word_eq := by
    intro s t h
    obtain ⟨finish, block, _⟩ := blocks s t h
    exact block.output

end PASoundness
