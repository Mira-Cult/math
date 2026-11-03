import Shared.PNP.Record285.GrammarCoreZeroSound
import Shared.PNP.Record285.GrammarRegisterInterface

/-! Connect the all-natural abstract transfers to the complete list-based
register bank, including appended normalization zeros. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarRegisterInterface

theorem drop_head_getD (fields : List Nat) (i : Nat) :
    (fields.drop i).headD 0 = fields.getD i 0 := by
  induction fields generalizing i with
  | nil => cases i <;> rfl
  | cons a rest ih => cases i with
    | zero => rfl
    | succ i => simp [List.drop]

theorem split_at (fields : List Nat) (i : Nat) (hi : i < fields.length) :
    fields = fields.take i ++ [fields[i]] ++ fields.drop (i+1) := by
  have h := List.take_append_drop i fields
  rw [List.drop_eq_getElem_cons hi] at h
  simp at h ⊢

theorem set_at (fields : List Nat) (i value : Nat) (hi : i < fields.length) :
    fields.set i value = fields.take i ++ [value] ++ fields.drop (i+1) := by
  simp [List.set_eq_take_append_cons_drop,hi]

/-- An arithmetic update changes exactly its selected existing register;
all extra cells, if any, are appended zeros. -/
theorem arithmetic_normal_form (e : Edge) (fields : List Nat) (i : Nat)
    (hi : i < fields.length) (hindex : operationIndex e = some i) :
    ∃ extra, applyUpdate e fields =
      fields.set i (operationValue e fields[i]) ++ List.replicate extra 0 := by
  let before := fields.take i
  let after := fields.drop (i+1)
  have hlen : before.length = i := by simp [before,List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
  have hf : fields = before ++ [fields[i]] ++ after := split_at fields i hi
  have hset (value : Nat) : fields.set i value = before ++ [value] ++ after := set_at fields i value hi
  cases e with
  | inc j =>
    simp only [operationIndex,Option.some.injEq] at hindex
    subst j
    refine ⟨0,?_⟩
    simp only [operationValue,hset,List.replicate_zero,List.append_nil]
    have h := increment_split before after fields[i]
    rw [hlen] at h
    exact (congrArg (applyUpdate (.inc i)) hf).trans h
  | dec j =>
    simp only [operationIndex,Option.some.injEq] at hindex
    subst j
    obtain ⟨extra,h⟩ := decrement_split before after fields[i]
    refine ⟨extra,?_⟩
    simp only [operationValue,hset]
    rw [hlen] at h
    exact (congrArg (applyUpdate (.dec i)) hf).trans h
  | half j =>
    simp only [operationIndex,Option.some.injEq] at hindex
    subst j
    obtain ⟨extra,h⟩ := half_split before after fields[i]
    refine ⟨extra,?_⟩
    simp only [operationValue,hset]
    rw [hlen] at h
    exact (congrArg (applyUpdate (.half i)) hf).trans h
  | node j => simp [operationIndex] at hindex
  | beep => simp [operationIndex] at hindex
  | brk j => simp [operationIndex] at hindex
  | cont j => simp [operationIndex] at hindex

theorem arithmetic_read (e : Edge) (fields : List Nat) (i j : Nat)
    (hi : i < fields.length) (hj : j < fields.length) (hindex : operationIndex e = some i) :
    (applyUpdate e fields).getD j 0 =
      if j = i then operationValue e (fields.getD i 0) else fields.getD j 0 := by
  obtain ⟨extra,h⟩ := arithmetic_normal_form e fields i hi hindex
  rw [h]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hj),List.getElem?_set]
  by_cases hij : i = j
  · subst j
    simp [hi]
  · simp [hij,Ne.symm hij]

theorem arithmetic_length (e : Edge) (fields : List Nat) (i : Nat)
    (hi : i < fields.length) (hindex : operationIndex e = some i) :
    fields.length ≤ (applyUpdate e fields).length := by
  obtain ⟨extra,h⟩ := arithmetic_normal_form e fields i hi hindex
  rw [h]
  simp

theorem nonarithmetic_update (e : Edge) (fields : List Nat) (h : operationIndex e = none) :
    applyUpdate e fields = fields := by
  cases e <;> simp_all [operationIndex,applyUpdate]

theorem bank_update_correct (e : Edge) (fields : List Nat)
    (hindex : ∀ i, operationIndex e = some i → i < fields.length)
    (j : Nat) (hj : j < fields.length) :
    (applyUpdate e fields).getD j 0 = updateBank e (fun i => fields.getD i 0) j := by
  cases he : operationIndex e with
  | none => simp [updateBank,he,nonarithmetic_update e fields he]
  | some i =>
    have hi := hindex i he
    simpa [updateBank,he] using arithmetic_read e fields i j hi hj he

theorem bank_length_nondecreasing (e : Edge) (fields : List Nat)
    (hindex : ∀ i, operationIndex e = some i → i < fields.length) :
    fields.length ≤ (applyUpdate e fields).length := by
  cases he : operationIndex e with
  | none => simp [nonarithmetic_update e fields he]
  | some i => exact arithmetic_length e fields i (hindex i he) he

theorem graph_test_matches (e : Edge) (fields : List Nat) :
    GrammarControlGraph.test e fields = operationBranch e (operandValue e (fun i => fields.getD i 0)) := by
  cases e <;> simp [GrammarControlGraph.test,operationBranch,operandValue,operationIndex]

theorem decrement_zero_identity (fields : List Nat) (i : Nat) (hi : i < fields.length)
    (hz : (fields.drop i).headD 0 = 0) : applyUpdate (.dec i) fields = fields := by
  have hdrop : fields.drop i = 0 :: fields.drop (i+1) := by
    have hd := List.drop_eq_getElem_cons hi
    have he : fields[i] = 0 := by simpa only [hd,List.headD_cons] using hz
    simpa only [he] using hd
  have hs := List.take_append_drop i fields
  rw [hdrop] at hs
  simp only [applyUpdate,hdrop,List.headD_cons,List.tail_cons,
    Shared.PNP.Record285.CleanBank.decrementFields]
  simpa using hs

end Shared.PNP.Record285.GrammarCoreZero
