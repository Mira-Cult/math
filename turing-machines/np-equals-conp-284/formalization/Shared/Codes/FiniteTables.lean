import Shared.ComplexityBridge.TM2Poly

/-! Numeric tables for finite TM2 operations. These tables do not encode
TM2 statement trees or establish a machine simulation or cost bound. -/

namespace Shared.Codes.FiniteTables

/-- A missing row or entry is invalid, never an implicit result. -/
def lookup (table : List Nat) (i : Nat) : Option Nat := table[i]?
def lookup₂ (table : List (List Nat)) (i j : Nat) : Option Nat :=
  (table[i]?).bind fun row => row[j]?

def table₁ {n : Nat} (f : Fin n → Nat) : List Nat := List.ofFn f
def table₂ {m n : Nat} (f : Fin m → Fin n → Nat) : List (List Nat) :=
  List.ofFn fun i => List.ofFn (f i)

@[simp] theorem lookup_table₁ {n : Nat} (f : Fin n → Nat) (i : Fin n) :
    lookup (table₁ f) i.val = some (f i) := by
  simp [lookup, table₁, i.isLt]

@[simp] theorem lookup_table₂ {m n : Nat} (f : Fin m → Fin n → Nat) (i : Fin m) (j : Fin n) :
    lookup₂ (table₂ f) i.val j.val = some (f i j) := by
  simp [lookup₂, table₂, i.isLt, j.isLt]

/-- Reification is a mathematical existence proof; lookup itself is executable. -/
theorem covers_unary {α β : Type} {m n : Nat} (ea : α ≃ Fin m) (eb : β ≃ Fin n)
    (f : α → β) : ∃ table : List Nat, ∀ a, lookup table (ea a).val = some (eb (f a)).val := by
  refine ⟨table₁ (fun i => (eb (f (ea.symm i))).val), ?_⟩
  intro a
  simp

theorem covers_binary {α β γ : Type} {m n p : Nat} (ea : α ≃ Fin m)
    (eb : β ≃ Fin n) (ec : γ ≃ Fin p) (f : α → β → γ) :
    ∃ table : List (List Nat), ∀ a b,
      lookup₂ table (ea a).val (eb b).val = some (ec (f a b)).val := by
  refine ⟨table₂ (fun i j => (ec (f (ea.symm i) (eb.symm j))).val), ?_⟩
  intro a b
  simp

theorem lookup_primrec : Primrec₂ lookup := Primrec.list_getElem?

theorem lookup₂_primrec : Primrec (fun p : (List (List Nat) × Nat) × Nat =>
    lookup₂ p.1.1 p.1.2 p.2) := by
  have hrow : Primrec (fun p : (List (List Nat) × Nat) × Nat => p.1.1[p.1.2]?) :=
    Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hcell : Primrec₂ (fun p : (List (List Nat) × Nat) × Nat => fun row : List Nat => row[p.2]?) :=
    (Primrec.list_getElem?.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  exact Primrec.option_bind hrow hcell

def decode₁ (e : Nat) : Option (List Nat) := Encodable.decode e
def decode₂ (e : Nat) : Option (List (List Nat)) := Encodable.decode e

theorem decode₁_computable : Computable decode₁ := Computable.decode
theorem decode₂_computable : Computable decode₂ := Computable.decode

theorem decode₁_coverage (t : List Nat) : ∃ e, decode₁ e = some t :=
  ⟨Encodable.encode t, Encodable.encodek t⟩
theorem decode₂_coverage (t : List (List Nat)) : ∃ e, decode₂ e = some t :=
  ⟨Encodable.encode t, Encodable.encodek t⟩

/-- The enumeration reaches a table representing every finite binary operation.
The equivalences and existence proof may use classical choice; the decoder and
lookup above operate only on finite numeric data. -/
theorem finite_binary_enumerated {α β γ : Type} [Finite α] [Finite β] [Finite γ]
    (f : α → β → γ) :
    ∃ (m n p : Nat) (ea : α ≃ Fin m) (eb : β ≃ Fin n) (ec : γ ≃ Fin p)
      (code : Nat) (table : List (List Nat)),
      decode₂ code = some table ∧ ∀ a b,
        lookup₂ table (ea a).val (eb b).val = some (ec (f a b)).val := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let : Fintype β := Fintype.ofFinite β
  let : Fintype γ := Fintype.ofFinite γ
  let ea := Fintype.equivFin α
  let eb := Fintype.equivFin β
  let ec := Fintype.equivFin γ
  obtain ⟨table, h⟩ := covers_binary ea eb ec f
  obtain ⟨code, hc⟩ := decode₂_coverage table
  exact ⟨_, _, _, ea, eb, ec, code, table, hc, h⟩

example : lookup [] 0 = none := by decide
example : lookup₂ [[3, 5], [7]] 0 1 = some 5 := by decide
example : lookup₂ [[3, 5], [7]] 1 1 = none := by decide
example : lookup₂ [[3, 5], [7]] 2 0 = none := by decide

end Shared.Codes.FiniteTables
