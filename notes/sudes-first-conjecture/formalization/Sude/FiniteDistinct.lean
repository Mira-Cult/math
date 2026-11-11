import Mathlib.Data.List.Nodup
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-! Kernel-checkable finite injectivity by a structurally recursive bit trie.
Hash collisions can only reject a valid input; acceptance proves distinctness. -/
namespace Sude

inductive DistinctTrie where
  | empty | full | fork (left right : DistinctTrie)

def DistinctTrie.contains : ℕ → DistinctTrie → ℕ → Bool
  | _, .empty, _ => false
  | _, .full, _ => true
  | 0, .fork _ _, _ => false
  | depth + 1, .fork left right, n =>
    if n % 2 = 0 then contains depth left (n / 2) else contains depth right (n / 2)

def DistinctTrie.insert : ℕ → DistinctTrie → ℕ → DistinctTrie
  | 0, _, _ => .full
  | _ + 1, .full, _ => .full
  | depth + 1, .empty, n =>
    if n % 2 = 0 then .fork (insert depth .empty (n / 2)) .empty
    else .fork .empty (insert depth .empty (n / 2))
  | depth + 1, .fork left right, n =>
    if n % 2 = 0 then .fork (insert depth left (n / 2)) right
    else .fork left (insert depth right (n / 2))

theorem DistinctTrie.contains_insert_self (depth : ℕ) (t : DistinctTrie) (n : ℕ) :
    contains depth (insert depth t n) n = true := by
  induction depth generalizing t n with
  | zero => simp [insert, contains]
  | succ depth ih =>
    cases t <;> simp only [insert, contains]
    all_goals split <;> simp_all [contains]

theorem DistinctTrie.contains_insert_mono (depth : ℕ) (t : DistinctTrie) (n m : ℕ)
    (h : contains depth t m = true) : contains depth (insert depth t n) m = true := by
  induction depth generalizing t n m with
  | zero => simp [insert, contains]
  | succ depth ih =>
    cases t with
    | empty => simp [contains] at h
    | full => simp [insert, contains]
    | fork left right =>
      by_cases hn : n % 2 = 0 <;> by_cases hm : m % 2 = 0 <;>
        simp [insert, contains, hn, hm] at h ⊢
      all_goals first | exact h | exact ih _ _ _ h

def distinctTrieAux (depth : ℕ) : List ℕ → DistinctTrie → Bool
  | [], _ => true
  | n :: rest, t =>
    if DistinctTrie.contains depth t n then false
    else distinctTrieAux depth rest (DistinctTrie.insert depth t n)

/-- The strengthened invariant also says that all remaining inputs avoid
the starting trie; this makes cross-step collision accounting explicit. -/
theorem distinctTrieAux_sound (depth : ℕ) (xs : List ℕ) (t : DistinctTrie)
    (h : distinctTrieAux depth xs t = true) :
    xs.Nodup ∧ ∀ x ∈ xs, DistinctTrie.contains depth t x = false := by
  induction xs generalizing t with
  | nil => simp
  | cons a xs ih =>
    simp only [distinctTrieAux] at h
    split at h
    · contradiction
    · rename_i ha
      have ha' : DistinctTrie.contains depth t a = false := by
        cases hc : DistinctTrie.contains depth t a <;> simp_all
      have ⟨hnd, havoid⟩ := ih _ h
      have hanot : a ∉ xs := by
        intro haMem
        have hfalse := havoid a haMem
        rw [DistinctTrie.contains_insert_self] at hfalse
        contradiction
      refine ⟨List.nodup_cons.mpr ⟨hanot, hnd⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha'
      · have hfalse := havoid x hx
        cases hc : DistinctTrie.contains depth t x with
        | false => rfl
        | true =>
          have ht := DistinctTrie.contains_insert_mono depth t a x hc
          rw [ht] at hfalse
          contradiction

def finiteDistinctCheck {n : ℕ} (depth : ℕ) (f : Fin n → ℕ) : Bool :=
  distinctTrieAux depth (List.ofFn f) .empty

theorem finiteDistinctCheck_sound {n : ℕ} (depth : ℕ) (f : Fin n → ℕ)
    (h : finiteDistinctCheck depth f = true) : Function.Injective f := by
  have hn : (List.ofFn f).Nodup := (distinctTrieAux_sound depth _ _ h).1
  rw [List.ofFn_eq_map] at hn
  have hi := (List.nodup_map_iff_inj_on (List.nodup_finRange n)).mp hn
  intro a b hab
  exact hi a (List.mem_finRange a) b (List.mem_finRange b) hab

theorem finiteDistinctCheck_equiv_sound {n : ℕ} {α : Type*}
    (depth : ℕ) (e : Fin n ≃ α) (f : α → ℕ)
    (h : finiteDistinctCheck depth (f ∘ e) = true) : Function.Injective f :=
  (e.injective_comp f).mp (finiteDistinctCheck_sound depth (f ∘ e) h)

def prefixEndpointIndexEquiv (P Q : ℕ) : ((Fin P × Fin Q) × Bool) ≃ Fin ((P * Q) * 2) :=
  (Equiv.prodCongr finProdFinEquiv finTwoEquiv.symm).trans finProdFinEquiv

end Sude
