import PASoundness.Cantor
import PASoundness.Producer

/-!
Total numeric syntax and quantifier-free matrix computation for the compact
PA238/HF producer. This does not assert that the compact calculus is PA.
The missing arithmetic interpretation and theorem-origin/coverage bridges
are separate obligations. No arbitrary program is used as a matrix language.
-/
namespace PASoundness.CompactMatrix
open PASoundness.Cantor

inductive Formula where
  | truth
  | imp : Formula → Formula → Formula
  | member : Nat → Nat → Formula
  | all : Nat → Formula → Formula
  | equal : Nat → Nat → Formula
  deriving DecidableEq, Repr

/-- Every natural code decodes. Formula children are strictly smaller; variable
names are not recursively decoded. The special code zero denotes truth. -/
def decode (code : Nat) : Formula :=
  if code = 0 then .truth else
    let ab := unpair (code / 4)
    match code % 4 with
    | 0 => .imp (decode ab.1) (decode ab.2)
    | 1 => .member ab.1 ab.2
    | 2 => .all ab.1 (decode ab.2)
    | _ => .equal ab.1 ab.2
termination_by code
decreasing_by
  all_goals
    have h₁ := unpair_fst_le (code / 4)
    have h₂ := unpair_snd_le (code / 4)
    omega

/-- Exactly the source's repeated division-by-two atomic computation. -/
def bit : Nat → Nat → Bool
  | a, 0 => decide (a % 2 = 1)
  | a, b+1 => bit (a/2) b

theorem bit_eq_testBit (a b : Nat) : bit a b = a.testBit b := by
  induction b generalizing a with
  | zero => exact (Nat.testBit_zero a).symm
  | succ b ih => simp [bit, Nat.testBit_succ, ih]

@[simp] theorem bit_self_false (a : Nat) : bit a a = false := by
  rw [bit_eq_testBit]
  exact Nat.testBit_lt_two_pow Nat.lt_two_pow_self

abbrev Environment := Nat → Nat

def update (ρ : Environment) (x value : Nat) : Environment :=
  fun y => if y = x then value else ρ y

def Formula.Realize (ρ : Environment) : Formula → Prop
  | .truth => True
  | .imp a b => a.Realize ρ → b.Realize ρ
  | .member a b => bit (ρ a) (ρ b) = true
  | .all x a => ∀ value, a.Realize (update ρ x value)
  | .equal a b => ρ a = ρ b

def falsity : Formula := .member 0 0
def existsAt (x : Nat) (f : Formula) : Formula :=
  .imp (.all x (.imp f falsity)) falsity

@[simp] theorem falsity_false (ρ : Environment) : ¬ falsity.Realize ρ := by
  simp [falsity, Formula.Realize]

theorem existsAt_realize (x : Nat) (f : Formula) (ρ : Environment) :
    (existsAt x f).Realize ρ ↔ ∃ a, f.Realize (update ρ x a) := by
  classical
  simp [existsAt, Formula.Realize, falsity, Classical.not_forall]

/-- Syntactic suitability is independent of variable values. -/
def Formula.isQF : Formula → Bool
  | .truth | .member _ _ | .equal _ _ => true
  | .all _ _ => false
  | .imp a b => a.isQF && b.isQF

/-- Both implication children are checked, including the truth-irrelevant one. -/
def evalQF (ρ : Environment) : Formula → Option Bool
  | .truth => some true
  | .member a b => some (bit (ρ a) (ρ b))
  | .equal a b => some (decide (ρ a = ρ b))
  | .all _ _ => none
  | .imp a b => match evalQF ρ a, evalQF ρ b with
    | some av, some bv => some ((!av) || bv)
    | _, _ => none

theorem evalQF_valid (f : Formula) (ρ : Environment) :
    (evalQF ρ f).isSome = f.isQF := by
  induction f with
  | truth | member | equal | all => rfl
  | imp a b ia ib =>
    cases ha : evalQF ρ a <;> cases hb : evalQF ρ b <;>
      simp_all [evalQF, Formula.isQF]

theorem evalQF_correct {f : Formula} {ρ : Environment} {value : Bool}
    (h : evalQF ρ f = some value) : (value = true ↔ f.Realize ρ) := by
  induction f generalizing value with
  | truth => simp_all [evalQF, Formula.Realize]
  | member a b => simpa [evalQF, Formula.Realize] using h.symm
  | equal a b =>
    simp only [evalQF, Option.some.injEq] at h
    rw [← h]
    simp [Formula.Realize]
  | all x a ia => simp [evalQF] at h
  | imp a b ia ib =>
    cases ha : evalQF ρ a with
    | none => simp [evalQF, ha] at h
    | some av =>
      cases hb : evalQF ρ b with
      | none => simp [evalQF, ha, hb] at h
      | some bv =>
        have hai := ia ha
        have hbi := ib hb
        simp only [evalQF, ha, hb, Option.some.injEq] at h
        rw [← h]
        cases av <;> cases bv <;> simp_all [Formula.Realize]

theorem evalQF_false_iff {f : Formula} {ρ : Environment} (hq : f.isQF = true) :
    evalQF ρ f = some false ↔ ¬ f.Realize ρ := by
  have hv := evalQF_valid f ρ
  cases he : evalQF ρ f with
  | none => simp_all
  | some b =>
    have ht := evalQF_correct he
    cases b <;> simp_all

/-- Rejects every pattern except the producer's literal existential abbreviation. -/
def peelExists : Formula → Option (Nat × Formula)
  | .imp (.all x (.imp f (.member 0 0))) (.member 0 0) => some (x, f)
  | _ => none

def peelAll : Formula → Option (Nat × Formula)
  | .all x f => some (x, f)
  | _ => none

theorem peelExists_exact {f : Formula} {x : Nat} {g : Formula}
    (h : peelExists f = some (x,g)) : f = existsAt x g := by
  cases f <;> try simp [peelExists] at h
  case imp a b =>
    cases a <;> try simp [peelExists] at h
    case all y a =>
      cases a <;> try simp [peelExists] at h
      case imp c d =>
        cases d <;> try simp [peelExists] at h
        case member u v =>
          cases u <;> cases v <;> try simp [peelExists] at h
          cases b <;> try simp [peelExists] at h
          case member u v =>
            cases u <;> cases v <;> try simp [peelExists] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl

theorem peelAll_exact {f : Formula} {x : Nat} {g : Formula}
    (h : peelAll f = some (x,g)) : f = .all x g := by
  cases f <;> simp_all [peelAll]

structure NormalForm where
  binders : List Nat
  matrix : Formula
  deriving DecidableEq, Repr

def peel (q : Polarity) (f : Formula) : Option (Nat × Formula) :=
  match q with | .ex => peelExists f | .all => peelAll f

/-- Recognize positive or zero singleton rank. No closedness check is added:
the pinned producer gives unbound names the value zero and honors shadowing. -/
def normalize : Polarity → Nat → Formula → Option NormalForm
  | _, 0, f => if f.isQF then some ⟨[], f⟩ else none
  | q, n+1, f =>
    (peel q f).bind fun (x,g) => (normalize q.flip n g).map fun r =>
      ⟨x :: r.binders, r.matrix⟩

def bind : List Nat → List Nat → Environment → Environment
  | x::xs, value::values, ρ => bind xs values (update ρ x value)
  | _, _, ρ => ρ

theorem normalize_properties {q : Polarity} {n : Nat} {f : Formula} {r : NormalForm}
    (h : normalize q n f = some r) : r.binders.length = n ∧ r.matrix.isQF = true := by
  induction n generalizing q f r with
  | zero =>
    simp only [normalize] at h
    split at h
    next hq => cases h; exact ⟨rfl, hq⟩
    next hq => contradiction
  | succ n ih =>
    simp only [normalize, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨x,g⟩, hp, r', hr, he⟩ := h
    cases he
    obtain ⟨hlen, hq⟩ := ih hr
    exact ⟨by simp [hlen], hq⟩

/-- Prefix recognition has its ordinary quantified meaning, including repeated
binder names with newest-binding shadowing and free names interpreted by ρ. -/
theorem normalize_semantics {q : Polarity} {n : Nat} {f : Formula} {r : NormalForm}
    (h : normalize q n f = some r) (ρ : Environment) :
    f.Realize ρ ↔ altPrefix q n (fun xs => r.matrix.Realize (bind r.binders xs ρ)) := by
  induction n generalizing q f r ρ with
  | zero =>
    simp only [normalize] at h
    split at h
    next hq => cases h; rfl
    next hq => contradiction
  | succ n ih =>
    simp only [normalize, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨x,g⟩, hp, r', hr, he⟩ := h
    cases he
    cases q with
    | ex =>
      have hf := peelExists_exact hp
      rw [hf, existsAt_realize]
      change (∃ a, g.Realize (update ρ x a)) ↔
        ∃ a, altPrefix .all n
          (fun xs => r'.matrix.Realize (bind r'.binders xs (update ρ x a)))
      apply exists_congr
      intro a
      exact ih hr (update ρ x a)
    | all =>
      have hf := peelAll_exact hp
      rw [hf]
      change (∀ a, g.Realize (update ρ x a)) ↔
        ∀ a, altPrefix .ex n
          (fun xs => r'.matrix.Realize (bind r'.binders xs (update ρ x a)))
      apply forall_congr'
      intro a
      exact ih hr (update ρ x a)

def valid (conclusion : Nat → Nat) (n p : Nat) : Prop :=
  (normalize .ex n (decode (conclusion p))).isSome = true

def matrixTruth (conclusion : Nat → Nat) (n p : Nat) (xs : List Nat) : Prop :=
  match normalize .ex n (decode (conclusion p)) with
  | none => True
  | some r => r.matrix.Realize (bind r.binders xs (fun _ => 0))

def record (conclusion : Nat → Nat) (rank certificate : Nat) (xs : List Nat) : Bool :=
  if xs.length ≠ rank then false else
    match normalize .ex rank (decode (conclusion certificate)) with
    | none => false
    | some r => match evalQF (bind r.binders xs (fun _ => 0)) r.matrix with
      | none => false
      | some value => !value

/-- The computed emitted bit has the required validity-and-false-matrix
specification. No soundness premise occurs, and validity is tuple independent. -/
theorem record_spec (conclusion : Nat → Nat) (n p : Nat) (xs : List Nat)
    (hlen : xs.length = n) :
    record conclusion n p xs = true ↔ valid conclusion n p ∧ ¬ matrixTruth conclusion n p xs := by
  simp only [record, hlen, ne_eq, not_true_eq_false, if_false]
  cases hn : normalize .ex n (decode (conclusion p)) with
  | none => simp [valid, matrixTruth, hn]
  | some r =>
    have hq := (normalize_properties hn).2
    have hv := evalQF_valid r.matrix (bind r.binders xs (fun _ => 0))
    cases he : evalQF (bind r.binders xs (fun _ => 0)) r.matrix with
    | none => simp_all
    | some value =>
      have ht := evalQF_correct he
      cases value <;> simp_all [valid, matrixTruth]

theorem malformed_tuple_zero (conclusion : Nat → Nat) (n p : Nat) (xs : List Nat)
    (h : xs.length ≠ n) : record conclusion n p xs = false := by
  simp [record, h]

theorem invalid_normalization_zero (conclusion : Nat → Nat) (n p : Nat) (xs : List Nat)
    (h : normalize .ex n (decode (conclusion p)) = none) :
    record conclusion n p xs = false := by
  simp [record, h]

/-- A false implication antecedent does not permit a quantified child to
escape the syntactic matrix check. -/
example : evalQF (fun _ => 0) (.imp falsity (.all 0 .truth)) = none := rfl
example : evalQF (fun x => x) (.equal 0 1) = some false := rfl
example : bit 42 1 = true := rfl

end PASoundness.CompactMatrix
