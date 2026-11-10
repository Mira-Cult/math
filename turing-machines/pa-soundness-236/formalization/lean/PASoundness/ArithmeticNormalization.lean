import PASoundness.Peano
import PASoundness.Producer
import Mathlib.ModelTheory.Complexity

/-!
# Executable normalization of genuine arithmetic sentences

Mathlib's canonical `toPrenex` supplies capture-avoiding semantic prenex
normalization. Structural peeling then inserts unused singleton quantifiers
to obtain a positive existential-leading alternating rank. The finite matrix
evaluator computes only genuine quantifier-free arithmetic syntax. This is a
new reusable producer format, not the compact PA238/HF normalizer, and the
resulting singleton rank is not advertised as a semantic Sigma level.
-/

namespace PASoundness.ArithmeticNormalization

open FirstOrder FirstOrder.Language

abbrev ScopedFormula (n : Nat) := Peano.language.BoundedFormula Empty n

/-- A total syntax evaluator. The universal-constructor fallback returns
false; normalization proves only quantifier-free leaves are evaluated, so
this fallback is never reached on the certified matrix.
There is no language of arbitrary programs or unproved termination premise. -/
def evalQF : {n : Nat} → ScopedFormula n → (Fin n → Nat) → Bool
  | _, .falsum, _ => false
  | _, .equal t u, env => decide
      (t.realize (Sum.elim Empty.elim env) = u.realize (Sum.elim Empty.elim env))
  | _, .rel r _, _ => Empty.elim r
  | _, .imp φ ψ, env => !(evalQF φ env) || evalQF ψ env
  | _, .all _, _ => false

theorem evalQF_correct {n : Nat} {φ : ScopedFormula n} (h : φ.IsQF) (env : Fin n → Nat) :
    evalQF φ env = true ↔ φ.Realize Empty.elim env := by
  induction h with
  | falsum => simp [evalQF, BoundedFormula.Realize]
  | of_isAtomic h =>
    cases h with
    | equal t u => simp [evalQF, Term.bdEqual, BoundedFormula.Realize]
    | rel r ts => exact Empty.elim r
  | imp hφ hψ ihφ ihψ =>
    simp only [evalQF, Bool.or_eq_true, Bool.not_eq_true', ihψ, BoundedFormula.realize_imp]
    rw [← ihφ]
    cases evalQF _ env <;> simp

/-- One leaf dummy keeps every advertised rank positive. Repeated source
quantifiers are separated by unused opposite-polarity singleton coordinates. -/
def rankAux : {n : Nat} → Polarity → ScopedFormula n → Nat
  | _, .ex, BoundedFormula.ex φ => rankAux .all φ + 1
  | _, .all, BoundedFormula.ex φ => rankAux .all φ + 2
  | _, .all, .all φ => rankAux .ex φ + 1
  | _, .ex, .all φ => rankAux .ex φ + 2
  | _, _, _ => 1

/-- Consume real quantifier coordinates in bound-variable order, skipping
exactly the inserted dummies. All out-of-range list reads return zero; on a
generated alternating prefix every read has the advertised finite length. -/
def matrixAux : {n : Nat} → Polarity → ScopedFormula n → (Fin n → Nat) → List Nat → Bool
  | _, .ex, BoundedFormula.ex φ, env, xs =>
      matrixAux .all φ (Fin.snoc env (xs.headD 0)) xs.tail
  | _, .all, BoundedFormula.ex φ, env, xs =>
      matrixAux .all φ (Fin.snoc env (xs.tail.headD 0)) xs.tail.tail
  | _, .all, .all φ, env, xs =>
      matrixAux .ex φ (Fin.snoc env (xs.headD 0)) xs.tail
  | _, .ex, .all φ, env, xs =>
      matrixAux .ex φ (Fin.snoc env (xs.tail.headD 0)) xs.tail.tail
  | _, _, φ, env, _ => evalQF φ env

theorem qf_compile {n : Nat} {φ : ScopedFormula n} (h : φ.IsQF)
    (q : Polarity) (env : Fin n → Nat) (xs : List Nat) :
    rankAux q φ = 1 ∧ matrixAux q φ env xs = evalQF φ env := by
  cases h with
  | falsum => cases q <;> exact ⟨rfl,rfl⟩
  | of_isAtomic h => cases h <;> cases q <;> exact ⟨rfl,rfl⟩
  | imp hφ hψ =>
    cases hφ with
    | falsum => cases q <;> exact ⟨rfl,rfl⟩
    | of_isAtomic h => cases h <;> cases q <;> exact ⟨rfl,rfl⟩
    | imp h₁ h₂ => cases q <;> exact ⟨rfl,rfl⟩

theorem rankAux_pos {n : Nat} {φ : ScopedFormula n} (h : φ.IsPrenex) (q : Polarity) :
    0 < rankAux q φ := by
  induction h generalizing q with
  | of_isQF h =>
    rw [(qf_compile h q (fun _ => 0) []).1]
    decide
  | all h ih =>
    cases q with
    | ex => change 0 < rankAux .ex _ + 2; omega
    | all => change 0 < rankAux .ex _ + 1; omega
  | ex h ih =>
    cases q with
    | ex => change 0 < rankAux .all _ + 1; omega
    | all => change 0 < rankAux .all _ + 2; omega

/-- Semantic compilation of any canonical prenex arithmetic formula, with
all existing parameters and bound-variable assignments preserved. -/
theorem prenex_semantics {n : Nat} {φ : ScopedFormula n} (h : φ.IsPrenex)
    (q : Polarity) (env : Fin n → Nat) :
    φ.Realize Empty.elim env ↔
      altPrefix q (rankAux q φ) (fun xs => matrixAux q φ env xs = true) := by
  induction h generalizing q with
  | @of_isQF n φ h =>
    have hr := (qf_compile h q env []).1
    have hm : matrixAux q φ env = fun _ => evalQF φ env := by
      funext xs
      exact (qf_compile h q env xs).2
    rw [hr, hm, altPrefix_constant]
    exact (evalQF_correct h env).symm
  | @all n φ h ih =>
    cases q with
    | all =>
      change (∀ x : Nat, φ.Realize Empty.elim (Fin.snoc env x)) ↔
        ∀ x : Nat, altPrefix .ex (rankAux .ex φ)
          (fun xs => matrixAux .ex φ (Fin.snoc env x) xs = true)
      exact forall_congr' (fun x => ih .ex (Fin.snoc env x))
    | ex =>
      change (∀ x : Nat, φ.Realize Empty.elim (Fin.snoc env x)) ↔
        ∃ _ : Nat, ∀ x : Nat, altPrefix .ex (rankAux .ex φ)
          (fun xs => matrixAux .ex φ (Fin.snoc env x) xs = true)
      constructor
      · intro hh
        exact ⟨0, fun x => (ih .ex (Fin.snoc env x)).mp (hh x)⟩
      · rintro ⟨_, hh⟩ x
        exact (ih .ex (Fin.snoc env x)).mpr (hh x)
  | @ex n φ h ih =>
    rw [BoundedFormula.realize_ex]
    cases q with
    | ex =>
      change (∃ x : Nat, φ.Realize Empty.elim (Fin.snoc env x)) ↔
        ∃ x : Nat, altPrefix .all (rankAux .all φ)
          (fun xs => matrixAux .all φ (Fin.snoc env x) xs = true)
      exact exists_congr (fun x => ih .all (Fin.snoc env x))
    | all =>
      change (∃ x : Nat, φ.Realize Empty.elim (Fin.snoc env x)) ↔
        ∀ _ : Nat, ∃ x : Nat, altPrefix .all (rankAux .all φ)
          (fun xs => matrixAux .all φ (Fin.snoc env x) xs = true)
      constructor
      · rintro ⟨x,hx⟩ _
        exact ⟨x, (ih .all (Fin.snoc env x)).mp hx⟩
      · intro hh
        obtain ⟨x,hx⟩ := hh 0
        exact ⟨x, (ih .all (Fin.snoc env x)).mpr hx⟩

/-- Positive alternating singleton rank of the actual canonical normal form. -/
def rank (φ : Peano.Sentence) : Nat := rankAux .ex φ.toPrenex

/-- Executable finite matrix; no proof object or semantic oracle is read. -/
def matrix (φ : Peano.Sentence) (xs : List Nat) : Bool :=
  matrixAux .ex φ.toPrenex Fin.elim0 xs

theorem rank_pos (φ : Peano.Sentence) : 0 < rank φ :=
  rankAux_pos φ.toPrenex_isPrenex .ex

/-- Closed semantic normalization. A producer may retain a proof of the
original sentence; it need not assert that a proof of the normalized syntax
has already been reconstructed in the object calculus. -/
theorem semantics (φ : Peano.Sentence) :
    (Nat ⊨ φ) ↔ altPrefix .ex (rank φ) (fun xs => matrix φ xs = true) := by
  have hp := prenex_semantics φ.toPrenex_isPrenex .ex (Fin.elim0 : Fin 0 → Nat)
  rw [BoundedFormula.realize_toPrenex] at hp
  simp only [rank, matrix, FirstOrder.Language.Sentence.Realize,
    FirstOrder.Language.Formula.Realize]
  convert hp using 2

theorem rank_bot : rank (⊥ : Peano.Sentence) = 1 := rfl

theorem matrix_bot (xs : List Nat) : matrix (⊥ : Peano.Sentence) xs = false := rfl

/-- A scope-sensitive arithmetic fixture: forall x, exists y, y = S(x). -/
def scopeFixture : Peano.Sentence :=
  BoundedFormula.all (BoundedFormula.ex
    (BoundedFormula.equal (.var (.inr 1)) (.func .succ ![.var (.inr 0)])))

theorem scopeFixture_rank : rank scopeFixture = 4 := by decide

/-- The real witnesses occupy coordinates one and two; the outer and final
dummy coordinates have no arithmetic role. -/
theorem scopeFixture_hit : matrix scopeFixture [37, 4, 5, 99] = true := by decide

theorem scopeFixture_miss : matrix scopeFixture [37, 4, 6, 99] = false := by decide

end PASoundness.ArithmeticNormalization
