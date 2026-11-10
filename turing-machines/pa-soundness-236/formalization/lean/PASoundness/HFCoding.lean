import PASoundness.CompactSemantics
import Mathlib.Data.Finset.Sort

/-!
# Explicit hereditarily finite objects and their binary codes

`Object` is a separate represented domain. Membership is well founded, every
object has finitely many members, extensionality holds, and assembling those
members is inverse to decomposition. These facts justify the HF interpretation
of the compact bit structure. Natural arithmetic values are embedded as finite
von Neumann ordinals; that embedding is not the identity on codes.
-/

namespace PASoundness.HFCoding
open CompactMatrix

structure Object where
  code : Nat
  deriving DecidableEq, Repr

theorem code_injective : Function.Injective Object.code := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

def Mem (x a : Object) : Prop := bit a.code x.code = true

instance : Membership Object Object := ⟨fun a x => Mem x a⟩
instance (x a : Object) : Decidable (x ∈ a) := inferInstanceAs (Decidable (bit a.code x.code = true))

theorem member_code_lt {x a : Object} (h : x ∈ a) : x.code < a.code :=
  CompactSemantics.member_lt a.code x.code h

theorem membership_wellFounded : WellFounded (fun x a : Object => x ∈ a) :=
  (measure Object.code).wf.mono (fun _ _ h => member_code_lt h)

theorem not_mem_self (a : Object) : ¬ a ∈ a :=
  fun h => Nat.lt_irrefl _ (member_code_lt h)

theorem ext {a b : Object} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  apply code_injective
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := h ⟨i⟩
  change (bit a.code i = true ↔ bit b.code i = true) at hi
  rw [bit_eq_testBit, bit_eq_testBit] at hi
  exact Bool.eq_iff_iff.mpr hi

def elements (a : Object) : Finset Object :=
  ((Finset.range a.code).filter (fun i => bit a.code i = true)).image Object.mk

@[simp] theorem mem_elements (x a : Object) : x ∈ elements a ↔ x ∈ a := by
  cases x with
  | mk i =>
    simp only [elements, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      Object.mk.injEq, exists_eq_right]
    constructor
    · exact And.right
    · intro h
      exact ⟨CompactSemantics.member_lt _ _ h,h⟩

/-- Canonical finite assembly; sorting only fixes an executable list order.
The resulting object is independent of the order because membership is exact. -/
def assemble (xs : Finset Object) : Object :=
  ⟨CompactSemantics.finiteSetCode ((xs.image Object.code).sort (· ≤ ·))⟩

@[simp] theorem mem_assemble (x : Object) (xs : Finset Object) :
    x ∈ assemble xs ↔ x ∈ xs := by
  change bit (CompactSemantics.finiteSetCode _) x.code = true ↔ _
  rw [CompactSemantics.finiteSetCode_spec]
  simp only [Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨y,hy,he⟩
    exact code_injective he ▸ hy
  · intro h
    exact ⟨x,h,rfl⟩

@[simp] theorem assemble_elements (a : Object) : assemble (elements a) = a := by
  apply ext
  intro x
  simp

@[simp] theorem elements_assemble (xs : Finset Object) : elements (assemble xs) = xs := by
  ext x
  simp

/-- The represented HF domain is explicitly equivalent to its finite member
sets; this theorem does not identify either type with formula or proof codes. -/
def finitePowersetEquiv : Object ≃ Finset Object where
  toFun := elements
  invFun := assemble
  left_inv := assemble_elements
  right_inv := elements_assemble

def empty : Object := ⟨0⟩

@[simp] theorem not_mem_empty (x : Object) : ¬ x ∈ empty := by
  simp [Membership.mem, Mem, empty, bit_eq_testBit]

def successor (a : Object) : Object := assemble (insert a (elements a))

@[simp] theorem mem_successor (x a : Object) : x ∈ successor a ↔ x = a ∨ x ∈ a := by
  simp [successor]

def ordinal : Nat → Object
  | 0 => empty
  | n+1 => successor (ordinal n)

theorem ordinal_member {m n : Nat} (h : m < n) : ordinal m ∈ ordinal n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [ordinal, mem_successor]
    by_cases he : m = n
    · exact Or.inl (congrArg ordinal he)
    · exact Or.inr (ih (by omega))

theorem ordinal_code_strictMono : StrictMono (fun n => (ordinal n).code) :=
  fun _ _ h => member_code_lt (ordinal_member h)

theorem ordinal_injective : Function.Injective ordinal := by
  intro a b h
  exact ordinal_code_strictMono.injective (congrArg Object.code h)

theorem mem_ordinal (x : Object) (n : Nat) : x ∈ ordinal n ↔ ∃ m < n, x = ordinal m := by
  induction n with
  | zero => simp [ordinal]
  | succ n ih =>
    rw [ordinal, mem_successor, ih]
    constructor
    · rintro (h | ⟨m,hm,h⟩)
      · exact ⟨n,by omega,h⟩
      · exact ⟨m,by omega,h⟩
    · rintro ⟨m,hm,h⟩
      by_cases he : m = n
      · exact Or.inl (he ▸ h)
      · exact Or.inr ⟨m,by omega,h⟩

@[simp] theorem ordinal_mem_ordinal (m n : Nat) : ordinal m ∈ ordinal n ↔ m < n := by
  rw [mem_ordinal]
  constructor
  · rintro ⟨k,hk,he⟩
    exact ordinal_injective he ▸ hk
  · intro h
    exact ⟨m,h,rfl⟩

/-- Compact semantics over actual represented objects; `member a b` means
that the value of b belongs to the value of a. -/
def realizeHF (ρ : Nat → Object) : Formula → Prop
  | .truth => True
  | .imp a b => realizeHF ρ a → realizeHF ρ b
  | .member a b => ρ b ∈ ρ a
  | .equal a b => ρ a = ρ b
  | .all x a => ∀ value : Object, realizeHF (Function.update ρ x value) a

theorem code_update (ρ : Nat → Object) (x : Nat) (a : Object) :
    (fun y => (Function.update ρ x a y).code) =
      update (fun y => (ρ y).code) x a.code := by
  funext y
  by_cases h : y = x <;> simp [h,update]

theorem realizeHF_iff (f : Formula) (ρ : Nat → Object) :
    realizeHF ρ f ↔ f.Realize (fun x => (ρ x).code) := by
  induction f generalizing ρ with
  | truth | member => rfl
  | equal a b =>
    exact ⟨fun h => congrArg Object.code h, fun h => code_injective h⟩
  | imp a b ia ib => simp [realizeHF,Formula.Realize,ia,ib]
  | all x f ih =>
    simp only [realizeHF,Formula.Realize]
    constructor
    · intro h a
      have hh := (ih (Function.update ρ x ⟨a⟩)).mp (h ⟨a⟩)
      simpa only [code_update] using hh
    · intro h a
      apply (ih _).mpr
      rw [code_update]
      exact h a.code

theorem all_codes_are_objects (code : Nat) : ∃ a : Object, a.code = code := ⟨⟨code⟩,rfl⟩

theorem successor_code (a : Object) : (successor a).code = a.code ||| 2^a.code := by
  have hobj : successor a = ⟨a.code ||| 2^a.code⟩ := by
    apply ext
    intro x
    rw [mem_successor]
    change (x = a ∨ bit a.code x.code = true) ↔ bit (a.code ||| 2^a.code) x.code = true
    simp only [bit_eq_testBit,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,
      decide_eq_true_eq]
    have he : x = a ↔ x.code = a.code := ⟨congrArg Object.code,fun h => code_injective h⟩
    rw [he]
    tauto
  exact congrArg Object.code hobj

@[simp] theorem ordinal_succ_code (n : Nat) :
    (ordinal (n+1)).code = (ordinal n).code ||| 2^(ordinal n).code :=
  successor_code _

theorem ordinal_three_code : (ordinal 3).code = 11 := by
  rw [ordinal_succ_code 2,ordinal_succ_code 1,ordinal_succ_code 0]
  decide

theorem arithmetic_three_is_not_its_ordinal_code : (ordinal 3).code ≠ 3 := by
  rw [ordinal_three_code]
  decide

end PASoundness.HFCoding
