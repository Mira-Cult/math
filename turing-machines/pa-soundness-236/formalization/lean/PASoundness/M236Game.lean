import PASoundness.M236Observer
import PASoundness.Cantor

/-!
The selected strict-ordered-atom and Cantor-tagged H syntax, with the paid
atom slot and optimistic timeout. This is a mathematical finite-game
reference, not yet a simulation of the selected producer or its registers.
-/
namespace PASoundness.M236Game

open PASoundness.Cantor

def tag (f : Nat) : Nat := (unpair f).1
def payload (f : Nat) : Nat := (unpair f).2

theorem children_lt (f : Nat) (h : tag f ≠ 0) :
    tag f - 1 < f ∧ payload f < f := by
  have hp : pair (tag f) (payload f) = f := pair_unpair f
  have ht := triangle_ge (tag f + payload f)
  have hl := left_le_pair (tag f) (payload f)
  unfold pair at hp hl
  omega

/-- The atom P(j,g) reads membership of variable j in variable j+g+1.
Missing entries default to zero, as in the finite-environment source. -/
def atom (p : Nat) (env : List Nat) : Bool :=
  let j := (unpair p).1
  let gap := (unpair p).2
  (env.getD (j + gap + 1) 0).testBit (env.getD j 0)

/-- Standard truth of the actual H syntax on every natural code. -/
def Truth (f : Nat) (env : List Nat) : Prop :=
  if h : tag f = 0 then atom (payload f) env = true
  else ¬ Truth (tag f - 1) (0 :: env) ∨
    ∃ x, ¬ Truth (payload f) (x :: env)
termination_by f
decreasing_by
  · exact (children_lt f h).1
  · exact (children_lt f h).2

def Signed (f : Nat) (env : List Nat) (negative : Bool) : Prop :=
  if negative then ¬ Truth f env else Truth f env

/-- A finite path takes a move before inspecting even an atomic constructor.
Missing a slot returns optimistic true for either sign. A positive H move k+1
binds k; a zero move takes the left child and binds zero. -/
def path (f : Nat) (env : List Nat) (negative : Bool) : List Nat → Bool
  | [] => true
  | move :: rest =>
    if h : tag f = 0 then (atom (payload f) env) != negative
    else if move = 0 then path (tag f - 1) (0 :: env) (!negative) rest
    else path (payload f) ((move - 1) :: env) (!negative) rest
termination_by f
decreasing_by
  · exact (children_lt f h).1
  · exact (children_lt f h).2

def owner (negative : Bool) : Polarity := if negative then .all else .ex

@[simp] theorem owner_flip (negative : Bool) : owner (!negative) = (owner negative).flip := by
  cases negative <;> rfl

def child (f move : Nat) : Nat :=
  if move = 0 then tag f - 1 else payload f

theorem child_lt (f move : Nat) (h : tag f ≠ 0) : child f move < f := by
  unfold child
  split
  · exact (children_lt f h).1
  · exact (children_lt f h).2

theorem truth_h (f : Nat) (env : List Nat) (h : tag f ≠ 0) :
    Truth f env ↔ ∃ move, ¬ Truth (child f move) ((move - 1) :: env) := by
  rw [Truth]
  simp only [h]
  constructor
  · rintro (hl | ⟨x, hr⟩)
    · refine ⟨0, ?_⟩
      simpa [child] using hl
    · refine ⟨x + 1, ?_⟩
      simpa [child] using hr
  · rintro ⟨move, hm⟩
    cases move with
    | zero => left; simpa [child] using hm
    | succ x => right; exact ⟨x, by simpa [child] using hm⟩

theorem signed_atom (f : Nat) (env : List Nat) (negative : Bool) (h : tag f = 0) :
    Signed f env negative ↔ ((atom (payload f) env) != negative) = true := by
  cases negative <;> cases hv : atom (payload f) env <;> simp [Signed, Truth, h, hv]

theorem signed_positive_h (f : Nat) (env : List Nat) (h : tag f ≠ 0) :
    Signed f env false ↔ ∃ move, Signed (child f move) ((move - 1) :: env) true := by
  simpa [Signed] using truth_h f env h

theorem signed_negative_h (f : Nat) (env : List Nat) (h : tag f ≠ 0) :
    Signed f env true ↔ ∀ move, Signed (child f move) ((move - 1) :: env) false := by
  classical
  simpa [Signed] using not_congr (truth_h f env h)

theorem path_h (f : Nat) (env : List Nat) (negative : Bool) (move : Nat)
    (rest : List Nat) (h : tag f ≠ 0) :
    path f env negative (move :: rest) =
      path (child f move) ((move - 1) :: env) (!negative) rest := by
  rw [path]
  simp only [h]
  by_cases hm : move = 0 <;> simp [child, hm]

/-- A paid atom slot makes its move vacuous, but absence of that slot is
optimistic even when the atom would be false. -/
theorem atom_game (f : Nat) (env : List Nat) (negative : Bool) (n : Nat)
    (h : tag f = 0) :
    altPrefix (owner negative) (n + 1) (fun xs => path f env negative xs = true) ↔
      Signed f env negative := by
  have hp (q : Polarity) (x : Nat) :
      altPrefix q n (fun xs => path f env negative (x :: xs) = true) ↔
        Signed f env negative := by
    calc
      _ ↔ altPrefix q n (fun _ => (atom (payload f) env != negative) = true) := by
        apply altPrefix_congr_length
        intro xs _
        simp [path, h]
      _ ↔ (atom (payload f) env != negative) = true := altPrefix_constant _ _ _
      _ ↔ Signed f env negative := (signed_atom f env negative h).symm
  cases negative with
  | false =>
    change (∃ x, altPrefix .all n (fun xs => path f env false (x :: xs) = true)) ↔ _
    simp only [hp, exists_const]
  | true =>
    change (∀ x, altPrefix .ex n (fun xs => path f env true (x :: xs) = true)) ↔ _
    simp only [hp, forall_const]

theorem game_positive_h (f : Nat) (env : List Nat) (n : Nat) (h : tag f ≠ 0) :
    altPrefix .ex (n + 1) (fun xs => path f env false xs = true) ↔
      ∃ m, altPrefix .all n
        (fun xs => path (child f m) ((m - 1) :: env) true xs = true) := by
  change (∃ m, altPrefix .all n (fun xs => path f env false (m :: xs) = true)) ↔ _
  apply exists_congr
  intro m
  apply altPrefix_congr_length
  intro xs _
  rw [path_h f env false m xs h]
  rfl

theorem game_negative_h (f : Nat) (env : List Nat) (n : Nat) (h : tag f ≠ 0) :
    altPrefix .all (n + 1) (fun xs => path f env true xs = true) ↔
      ∀ m, altPrefix .ex n
        (fun xs => path (child f m) ((m - 1) :: env) false xs = true) := by
  change (∀ m, altPrefix .ex n (fun xs => path f env true (m :: xs) = true)) ↔ _
  apply forall_congr'
  intro m
  apply altPrefix_congr_length
  intro xs _
  rw [path_h f env true m xs h]
  rfl

/-- Optimistic cutoffs preserve signed truth at every rank. Once at least
`f+1` constructor slots are available, the game is exact for every finite
code, environment and natural-valued strategy. -/
theorem game_bounds (f : Nat) : ∀ (env : List Nat) (negative : Bool) (n : Nat),
    (Signed f env negative →
      altPrefix (owner negative) n (fun xs => path f env negative xs = true)) ∧
    (f + 1 ≤ n →
      altPrefix (owner negative) n (fun xs => path f env negative xs = true) →
        Signed f env negative) := by
  induction f using Nat.strong_induction_on with
  | h f ih =>
    intro env negative n
    cases n with
    | zero =>
      constructor
      · intro _
        simp [altPrefix, path]
      · intro hn
        omega
    | succ n =>
      by_cases ht : tag f = 0
      · have ha := atom_game f env negative n ht
        exact ⟨ha.mpr, fun _ => ha.mp⟩
      · cases negative with
        | false =>
          change (Signed f env false →
            altPrefix .ex (n+1) (fun xs => path f env false xs = true)) ∧
            (f+1 ≤ n+1 → altPrefix .ex (n+1)
              (fun xs => path f env false xs = true) → Signed f env false)
          rw [signed_positive_h f env ht, game_positive_h f env n ht]
          constructor
          · rintro ⟨m, hm⟩
            exact ⟨m, (ih (child f m) (child_lt f m ht) _ true n).1 hm⟩
          · intro hn
            rintro ⟨m, hm⟩
            have hb : child f m + 1 ≤ n := by have := child_lt f m ht; omega
            exact ⟨m, (ih (child f m) (child_lt f m ht) _ true n).2 hb hm⟩
        | true =>
          change (Signed f env true →
            altPrefix .all (n+1) (fun xs => path f env true xs = true)) ∧
            (f+1 ≤ n+1 → altPrefix .all (n+1)
              (fun xs => path f env true xs = true) → Signed f env true)
          rw [signed_negative_h f env ht, game_negative_h f env n ht]
          constructor
          · intro hs m
            exact (ih (child f m) (child_lt f m ht) _ false n).1 (hs m)
          · intro hn hg m
            have hb : child f m + 1 ≤ n := by have := child_lt f m ht; omega
            exact (ih (child f m) (child_lt f m ht) _ false n).2 hb (hg m)

/-- Align a negative game with the fixed existential-leading observer.
A missing alignment slot has the same optimistic payoff as a timeout. -/
def aligned (f : Nat) (env : List Nat) (positive : Bool) (xs : List Nat) : Bool :=
  if positive then path f env false xs
  else match xs with
    | [] => true
    | _ :: rest => path f env true rest

/-- The selected finite record function on complete addresses. The first
coordinates are C and y; unsupported y and short prefixes output zero.
Unused suffix coordinates are irrelevant to this value. This is the
mathematical record specification, not yet a proved physical implementation. -/
def selectedValue (a : Observer.Address) : Bool :=
  if a.rank < 2 then false else
    match a.coordinates with
    | c :: y :: rest =>
      if a.rank - 2 < y then false
      else !(aligned a.certificate [y] (c.testBit y) rest)
    | _ => false

theorem aligned_optimistic (f : Nat) (env : List Nat) (positive : Bool) (n : Nat) :
    Signed f env (!positive) →
      altPrefix .ex n (fun xs => aligned f env positive xs = true) := by
  cases positive with
  | true =>
    exact (game_bounds f env false n).1
  | false =>
    cases n with
    | zero => intro _; rfl
    | succ n =>
      intro hs
      change ∃ x, altPrefix .all n (fun xs => path f env true xs = true)
      exact ⟨0, (game_bounds f env true n).1 hs⟩

theorem aligned_exact (f : Nat) (env : List Nat) (positive : Bool) (n : Nat)
    (hn : f + 2 ≤ n) :
    altPrefix .ex n (fun xs => aligned f env positive xs = true) ↔
      Signed f env (!positive) := by
  constructor
  · cases positive with
    | true =>
      exact (game_bounds f env false n).2 (by omega)
    | false =>
      cases n with
      | zero => omega
      | succ n =>
        change (∃ x, altPrefix .all n (fun xs => path f env true xs = true)) → _
        rintro ⟨_, hg⟩
        exact (game_bounds f env true n).2 (by omega) hg
  · exact aligned_optimistic f env positive n

/-- Instantiation of the general fair-record theorem for the selected finite
game specification; it does not bind the physical table to this source. -/
theorem selected_source_accept_iff_strategies :
    M236Observer.TraceAccept (Source.source selectedValue) ↔ ∀ n, 0 < n → ∀ f,
      ∃ s : M236Observer.Strategy .ex n,
        M236Observer.Winning s (fun xs => selectedValue ⟨n, f, xs⟩ = false) :=
  M236Observer.source_trace_accept_iff_strategies selectedValue

theorem selected_bounded (f r c y : Nat) (xs : List Nat) (hy : y ≤ r) :
    selectedValue ⟨r + 2, f, c :: y :: xs⟩ =
      !(aligned f [y] (c.testBit y) xs) := by
  simp [selectedValue, Nat.not_lt_of_ge hy]

theorem selected_unbounded (f r c y : Nat) (xs : List Nat) (hy : r < y) :
    selectedValue ⟨r + 2, f, c :: y :: xs⟩ = false := by
  simp [selectedValue, hy]

/-- Expands the first two fixed observer moves: one witness C is shared
across all y, and an out-of-support y has optimistic payoff. -/
theorem selected_rank_game (f r : Nat) :
    altPrefix .ex (r + 2) (fun xs => selectedValue ⟨r+2, f, xs⟩ = false) ↔
      ∃ c : Nat, ∀ y : Nat, y ≤ r →
        altPrefix .ex r (fun xs => aligned f [y] (c.testBit y) xs = true) := by
  change (∃ c, ∀ y, altPrefix .ex r
      (fun xs => selectedValue ⟨r+2, f, c :: y :: xs⟩ = false)) ↔ _
  apply exists_congr
  intro c
  constructor
  · intro h y hy
    have he : altPrefix .ex r
        (fun xs => selectedValue ⟨r+2, f, c :: y :: xs⟩ = false) ↔
        altPrefix .ex r (fun xs => aligned f [y] (c.testBit y) xs = true) := by
      apply altPrefix_congr_length
      intro xs _
      simp [selected_bounded f r c y xs hy]
    exact he.mp (h y)
  · intro h y
    by_cases hy : y ≤ r
    · have he : altPrefix .ex r
          (fun xs => selectedValue ⟨r+2, f, c :: y :: xs⟩ = false) ↔
          altPrefix .ex r (fun xs => aligned f [y] (c.testBit y) xs = true) := by
        apply altPrefix_congr_length
        intro xs _
        simp [selected_bounded f r c y xs hy]
      exact he.mpr (h y hy)
    · have hx : ∀ xs, selectedValue ⟨r+2, f, c :: y :: xs⟩ = false := by
        intro xs
        exact selected_unbounded f r c y xs (by omega)
      apply (altPrefix_congr_length .ex r _ (fun _ => True) ?_).mpr
        ((altPrefix_constant .ex r True).mpr trivial)
      intro xs _
      simp [hx]

/-- Every finite initial segment of a unary predicate's truth values has a
single finite bit-table witness. No uniform witness across bounds is required. -/
def FiniteTableFamily : Prop :=
  ∀ f A : Nat, ∃ c : Nat, ∀ y : Nat, y ≤ A → Signed f [y] (!(c.testBit y))

theorem selected_source_accept_iff_games :
    M236Observer.TraceAccept (Source.source selectedValue) ↔ ∀ n, 0 < n → ∀ f,
      altPrefix .ex n (fun xs => selectedValue ⟨n, f, xs⟩ = false) := by
  rw [selected_source_accept_iff_strategies]
  apply forall_congr'
  intro n
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro f
  exact M236Observer.strategy_iff _ _ _

/-- The selected mathematical source is accepted exactly when the finite
bit-table family holds. This is structural: no PA or K soundness premise is
used, and each bound gets its own witness. The connection of this family to
compact proofs, and the source to the physical machine, are separate. -/
theorem selected_source_accept_iff_finite_tables :
    M236Observer.TraceAccept (Source.source selectedValue) ↔ FiniteTableFamily := by
  rw [selected_source_accept_iff_games]
  constructor
  · intro h f A
    let r := A + (f + 2)
    have hg := h (r+2) (by omega) f
    obtain ⟨c, hc⟩ := (selected_rank_game f r).mp hg
    refine ⟨c, ?_⟩
    intro y hy
    have hyr : y ≤ r := by dsimp [r]; omega
    have hr : f + 2 ≤ r := by dsimp [r]; omega
    exact (aligned_exact f [y] (c.testBit y) r hr).mp (hc y hyr)
  · intro tables n hn f
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        change ∃ x, selectedValue ⟨1, f, [x]⟩ = false
        exact ⟨0, by simp [selectedValue]⟩
      | succ r =>
        have hgame : altPrefix .ex (r+2)
            (fun xs => selectedValue ⟨r+2, f, xs⟩ = false) := by
          apply (selected_rank_game f r).mpr
          obtain ⟨c, hc⟩ := tables f r
          exact ⟨c, fun y hy => aligned_optimistic f [y] (c.testBit y) r (hc y hy)⟩
        simpa [Nat.add_assoc] using hgame

/-- The producer stores positional environments by nested Cantor pairs with
zero as the empty tail. Lookup is structurally recursive on the requested
index, so arbitrarily large finite indices and values are admitted. -/
def lookup : Nat → Nat → Nat
  | e, 0 => if e = 0 then 0 else (unpair e).1
  | e, i + 1 => if e = 0 then 0 else lookup (unpair e).2 i

theorem lookup_zero (i : Nat) : lookup 0 i = 0 := by
  cases i <;> simp [lookup]

/-- A zero binding over an empty tail is indistinguishable from the default
empty environment, exactly as in the producer's pair encoding. -/
theorem lookup_pair (v e i : Nat) :
    lookup (pair v e) i = if i = 0 then v else lookup e (i - 1) := by
  by_cases hz : pair v e = 0
  · have hv : v = 0 := by have h := left_le_pair v e; omega
    have he : e = 0 := by have h := right_le_pair v e; omega
    subst v
    subst e
    cases i <;> simp [lookup, pair, triangle, lookup_zero]
  · cases i <;> simp [lookup, hz, unpair_pair]

def Represents (encoded : Nat) (env : List Nat) : Prop :=
  ∀ i, lookup encoded i = env.getD i 0

theorem represents_empty : Represents 0 [] := by
  intro i
  simp [lookup_zero]

theorem represents_cons {e : Nat} {env : List Nat} (h : Represents e env) (v : Nat) :
    Represents (pair v e) (v :: env) := by
  intro i
  cases i with
  | zero => simp [lookup_pair]
  | succ i => simpa [lookup_pair] using h i

theorem represents_initial (y : Nat) : Represents (pair y 0) [y] :=
  represents_cons represents_empty y

def encodedAtom (p e : Nat) : Bool :=
  let j := (unpair p).1
  let gap := (unpair p).2
  (lookup e (j + gap + 1)).testBit (lookup e j)

theorem atom_encoded (p e : Nat) (env : List Nat) (h : Represents e env) :
    encodedAtom p e = atom p env := by
  change ∀ i, lookup e i = env.getD i 0 at h
  simp only [encodedAtom, atom, h]

/-- Finite-path execution using the source's numeric environment representation.
This is still a direct mathematical reference, not register-code correctness. -/
def encodedPath (f e : Nat) (negative : Bool) : List Nat → Bool
  | [] => true
  | move :: rest =>
    if h : tag f = 0 then (encodedAtom (payload f) e) != negative
    else encodedPath (child f move) (pair (move - 1) e) (!negative) rest
termination_by f
decreasing_by exact child_lt f move h

theorem path_encoded (f : Nat) : ∀ (e : Nat) (env : List Nat)
    (negative : Bool) (moves : List Nat), Represents e env →
      encodedPath f e negative moves = path f env negative moves := by
  induction f using Nat.strong_induction_on with
  | h f ih =>
    intro e env negative moves he
    cases moves with
    | nil => simp [encodedPath, path]
    | cons move rest =>
      by_cases ht : tag f = 0
      · simp [encodedPath, path, ht, atom_encoded _ _ _ he]
      · rw [path_h f env negative move rest ht, encodedPath]
        simp only [ht]
        exact ih (child f move) (child_lt f move ht) _ _ _ _
          (represents_cons he (move - 1))

theorem initial_path_encoded (f y : Nat) (negative : Bool) (moves : List Nat) :
    encodedPath f (pair y 0) negative moves = path f [y] negative moves :=
  path_encoded f _ _ _ _ (represents_initial y)

def encodedAligned (f y : Nat) (positive : Bool) (xs : List Nat) : Bool :=
  if positive then encodedPath f (pair y 0) false xs
  else match xs with
    | [] => true
    | _ :: rest => encodedPath f (pair y 0) true rest

theorem encoded_aligned (f y : Nat) (positive : Bool) (xs : List Nat) :
    encodedAligned f y positive xs = aligned f [y] positive xs := by
  cases positive <;> cases xs <;> simp [encodedAligned, aligned, initial_path_encoded]

/-- Exact numerical-environment reference value, equal on every finite address
(including malformed ones) to the list-environment specification. -/
def selectedEncodedValue (a : Observer.Address) : Bool :=
  if a.rank < 2 then false else
    match a.coordinates with
    | c :: y :: rest =>
      if a.rank - 2 < y then false
      else !(encodedAligned a.certificate y (c.testBit y) rest)
    | _ => false

theorem selected_encoded_value (a : Observer.Address) :
    selectedEncodedValue a = selectedValue a := by
  cases a with
  | mk n f xs =>
    cases xs with
    | nil => simp [selectedEncodedValue, selectedValue]
    | cons c tail =>
      cases tail with
      | nil => simp [selectedEncodedValue, selectedValue]
      | cons y rest => simp [selectedEncodedValue, selectedValue, encoded_aligned]

end PASoundness.M236Game
