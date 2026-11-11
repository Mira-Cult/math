import Sude.FiniteDistinct

/-! Checked trie checkpoints compose without losing cross-chunk distinctness. -/
namespace Sude

deriving instance DecidableEq for DistinctTrie

/-- Insert a whole chunk, returning the resulting trie only if no inserted
value collides with a previous value at the chosen bit depth. -/
def DistinctTrie.advance (depth : ℕ) : DistinctTrie → List ℕ → Option DistinctTrie
  | t, [] => some t
  | t, x :: xs =>
    if contains depth t x then none else advance depth (insert depth t x) xs

theorem DistinctTrie.advance_append (depth : ℕ) (t : DistinctTrie) (xs ys : List ℕ) :
    advance depth t (xs ++ ys) = (advance depth t xs).bind (fun u => advance depth u ys) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, advance]
    split <;> simp_all

/-- Every successful checkpoint also satisfies the original Boolean
checker specification. -/
theorem DistinctTrie.advance_implies_check (depth : ℕ) (t u : DistinctTrie) (xs : List ℕ)
    (h : advance depth t xs = some u) : distinctTrieAux depth xs t = true := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [advance] at h
    by_cases hc : contains depth t x = true
    · simp [hc] at h
    · have hc' : contains depth t x = false := by cases e : contains depth t x <;> simp_all
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
      simp only [distinctTrieAux, hc', Bool.false_eq_true, ↓reduceIte]
      exact ih _ h

/-- The deterministic next state, useful when the chunk has already been
checked. This is computational data and carries no correctness by itself. -/
def DistinctTrie.insertAll (depth : ℕ) (t : DistinctTrie) (xs : List ℕ) : DistinctTrie :=
  xs.foldl (insert depth) t

theorem DistinctTrie.advance_of_check (depth : ℕ) (t : DistinctTrie) (xs : List ℕ)
    (h : distinctTrieAux depth xs t = true) :
    advance depth t xs = some (insertAll depth t xs) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [distinctTrieAux] at h
    by_cases hc : contains depth t x = true
    · simp [hc] at h
    · have hc' : contains depth t x = false := by cases e : contains depth t x <;> simp_all
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
      simpa [advance, insertAll, hc'] using ih _ h

/-- Each constructor carries a kernel-checkable exact state transition.
No claim about a checkpoint is assumed merely from its generated data. -/
inductive VerifiedTrieChunks (depth : ℕ) : DistinctTrie → List (List ℕ) → DistinctTrie → Prop
  | nil (t) : VerifiedTrieChunks depth t [] t
  | cons {t u v xs rest} :
      DistinctTrie.advance depth t xs = some u →
      VerifiedTrieChunks depth u rest v →
      VerifiedTrieChunks depth t (xs :: rest) v

theorem VerifiedTrieChunks.advance_flatten {depth : ℕ} {t u : DistinctTrie} {chunks : List (List ℕ)}
    (h : VerifiedTrieChunks depth t chunks u) :
    DistinctTrie.advance depth t chunks.flatten = some u := by
  induction h with
  | nil => rfl
  | @cons t u v xs rest hfirst hrest ih =>
    simp only [List.flatten_cons, DistinctTrie.advance_append, hfirst, Option.bind_some]
    exact ih

/-- Successful checkpoints prove global uniqueness, including across every
pair of different chunks. -/
theorem VerifiedTrieChunks.nodup {depth : ℕ} {t u : DistinctTrie} {chunks : List (List ℕ)}
    (h : VerifiedTrieChunks depth t chunks u) : chunks.flatten.Nodup := by
  have hc := DistinctTrie.advance_implies_check depth t u chunks.flatten h.advance_flatten
  exact (distinctTrieAux_sound depth chunks.flatten t hc).1

end Sude
