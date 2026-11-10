import PASoundness.Peano
import PASoundness.CompactMatrix
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Tactic.Ring

/-!
# The compact bit language inside ordinary arithmetic

The formulas below use only the genuine PA signature `0,S,+,*` and logical
equality. The binary-bit atom is expanded using a finite beta-coded doubling
sequence. No exponentiation symbol or semantic predicate is added to PA.

This file proves standard-model correspondence for all compact formulas,
including open formulas and shadowing. Object-level PA derivations of the
translated compact axioms are a separate obligation.
-/

namespace PASoundness.CompactArithmetic
open FirstOrder FirstOrder.Language
open Peano

def exAt (x : Nat) (φ : Peano.Formula) : Peano.Formula :=
  (FOL.allAt x φ.not).not

@[simp] theorem realize_exAt (x : Nat) (φ : Peano.Formula) (ρ : Nat → Nat) :
    (exAt x φ).Realize ρ ↔ ∃ a, φ.Realize (Function.update ρ x a) := by
  classical
  simp [exAt, FOL.realize_allAt, Classical.not_forall]

def v (x : Nat) : Peano.Term := .var x

def lessTemplate : Peano.Formula :=
  exAt 2 ((add (v 0) (succ (v 2))).equal (v 1))

def less (a b : Peano.Term) : Peano.Formula :=
  lessTemplate.subst (fun x => if x = 0 then a else if x = 1 then b else zero)

@[simp] theorem realize_lessTemplate (ρ : Nat → Nat) :
    lessTemplate.Realize ρ ↔ ρ 0 < ρ 1 := by
  simp only [lessTemplate, realize_exAt, Formula.realize_equal,
    realize_add, realize_succ, v, Term.realize_var]
  simp only [Function.update_of_ne (by decide : (0:Nat) ≠ 2),
    Function.update_of_ne (by decide : (1:Nat) ≠ 2), Function.update_self]
  constructor
  · rintro ⟨a, ha⟩; omega
  · intro h; exact ⟨ρ 1 - ρ 0 - 1, by omega⟩

@[simp] theorem realize_less (a b : Peano.Term) (ρ : Nat → Nat) :
    (less a b).Realize ρ ↔ a.realize ρ < b.realize ρ := by
  simp [less, FOL.realize_subst, realize_lessTemplate]

def modulus (c i : Peano.Term) : Peano.Term := succ (mul (succ i) c)

def betaTemplate : Peano.Formula :=
  exAt 4 (((v 0).equal (add (mul (v 4) (modulus (v 1) (v 2))) (v 3))) ⊓
    (less (v 3) (modulus (v 1) (v 2))))

def beta (b c i r : Peano.Term) : Peano.Formula :=
  betaTemplate.subst (fun x => match x with
    | 0 => b | 1 => c | 2 => i | 3 => r | _ => zero)

/-- The arithmetic relation expressed by `beta`; all its arguments are values,
not compact objects, formula codes, or proof codes. -/
def Beta (b c i r : Nat) : Prop :=
  ∃ q, b = q * ((i+1)*c+1) + r ∧ r < (i+1)*c+1

@[simp] theorem realize_betaTemplate (ρ : Nat → Nat) :
    betaTemplate.Realize ρ ↔ Beta (ρ 0) (ρ 1) (ρ 2) (ρ 3) := by
  simp [betaTemplate, Beta, modulus, v]

@[simp] theorem realize_beta (b c i r : Peano.Term) (ρ : Nat → Nat) :
    (beta b c i r).Realize ρ ↔ Beta (b.realize ρ) (c.realize ρ)
      (i.realize ρ) (r.realize ρ) := by
  simp [beta, FOL.realize_subst, realize_betaTemplate]

theorem beta_iff_mod (b c i r : Nat) :
    Beta b c i r ↔ b % ((i+1)*c+1) = r := by
  constructor
  · rintro ⟨q, rfl, hr⟩
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  · intro h
    refine ⟨b / ((i+1)*c+1), ?_, ?_⟩
    · rw [← h]
      simpa only [Nat.mul_comm] using (Nat.div_add_mod b ((i+1)*c+1)).symm
    · rw [← h]
      exact Nat.mod_lt _ (by omega)

theorem beta_unique {b c i r s : Nat} (hr : Beta b c i r) (hs : Beta b c i s) :
    r = s := (beta_iff_mod _ _ _ _).mp hr |>.symm.trans ((beta_iff_mod _ _ _ _).mp hs)

/-- Every actual finite list has arithmetic beta parameters. This is the
pinned mathlib beta lemma, with its pairing used only in the metatheory. -/
theorem beta_sequence (xs : List Nat) :
    ∃ b c, ∀ i : Fin xs.length, Beta b c i xs[i] := by
  refine ⟨(Nat.unpair (Nat.unbeta xs)).1, (Nat.unpair (Nat.unbeta xs)).2, ?_⟩
  intro i
  apply (beta_iff_mod _ _ _ _).mpr
  exact Nat.beta_unbeta_coe xs i

def pow2Template : Peano.Formula :=
  exAt 2 (exAt 3
    ((beta (v 2) (v 3) zero (succ zero)) ⊓
      ((beta (v 2) (v 3) (v 0) (v 1)) ⊓
        (FOL.allAt 4 ((less (v 4) (v 0)).imp
          (exAt 5 (exAt 6
            ((beta (v 2) (v 3) (v 4) (v 5)) ⊓
              ((beta (v 2) (v 3) (succ (v 4)) (v 6)) ⊓
                ((v 6).equal (add (v 5) (v 5))))))))))))

def pow2 (n p : Peano.Term) : Peano.Formula :=
  pow2Template.subst (fun x => if x = 0 then n else if x = 1 then p else zero)

def Pow2 (n p : Nat) : Prop :=
  ∃ b c, Beta b c 0 1 ∧ Beta b c n p ∧
    ∀ i, i < n → ∃ r s, Beta b c i r ∧ Beta b c (i+1) s ∧ s = r+r

@[simp] theorem realize_pow2Template (ρ : Nat → Nat) :
    pow2Template.Realize ρ ↔ Pow2 (ρ 0) (ρ 1) := by
  simp [pow2Template, Pow2, v]

@[simp] theorem realize_pow2 (n p : Peano.Term) (ρ : Nat → Nat) :
    (pow2 n p).Realize ρ ↔ Pow2 (n.realize ρ) (p.realize ρ) := by
  simp [pow2, FOL.realize_subst, realize_pow2Template]

theorem pow2_iff (n p : Nat) : Pow2 n p ↔ p = 2^n := by
  constructor
  · rintro ⟨b,c,hzero,hend,hstep⟩
    have hvalues : ∀ i, i ≤ n → Beta b c i (2^i) := by
      intro i
      induction i with
      | zero => intro _; simpa using hzero
      | succ i ih =>
        intro hi
        obtain ⟨r,s,hr,hs,hadd⟩ := hstep i (by omega)
        have he := beta_unique hr (ih (by omega))
        rw [he, ← two_mul, ← pow_succ'] at hadd
        simpa [hadd] using hs
    exact beta_unique hend (hvalues n le_rfl)
  · rintro rfl
    let xs := List.ofFn (fun i : Fin (n+1) => 2^i.val)
    obtain ⟨b,c,h⟩ := beta_sequence xs
    have hx (i : Nat) (hi : i ≤ n) : Beta b c i (2^i) := by
      have ht := h ⟨i, by simpa [xs] using Nat.lt_succ_of_le hi⟩
      simpa only [xs, Fin.getElem_fin, List.getElem_ofFn] using ht
    refine ⟨b,c,by simpa using hx 0 (by omega),hx n le_rfl,?_⟩
    intro i hi
    exact ⟨2^i,2^(i+1),hx i (by omega),hx (i+1) (by omega),by rw [pow_succ]; omega⟩

def bitTemplate : Peano.Formula :=
  exAt 2 ((pow2 (v 1) (v 2)) ⊓
    (exAt 3 (exAt 4
      (((v 0).equal (add (add (mul (v 3) (add (v 2) (v 2))) (v 2)) (v 4))) ⊓
        (less (v 4) (v 2))))))

def bitFormula (a x : Peano.Term) : Peano.Formula :=
  bitTemplate.subst (fun y => if y = 0 then a else if y = 1 then x else zero)

def Bit (a x : Nat) : Prop :=
  ∃ p, Pow2 x p ∧ ∃ q r, a = q*(p+p)+p+r ∧ r < p

@[simp] theorem realize_bitTemplate (ρ : Nat → Nat) :
    bitTemplate.Realize ρ ↔ Bit (ρ 0) (ρ 1) := by
  simp [bitTemplate, Bit, v]

@[simp] theorem realize_bitFormula (a x : Peano.Term) (ρ : Nat → Nat) :
    (bitFormula a x).Realize ρ ↔ Bit (a.realize ρ) (x.realize ρ) := by
  simp [bitFormula, FOL.realize_subst, realize_bitTemplate]

/-- The arithmetic atom and the total compact evaluator agree at every pair. -/
theorem bit_iff (a x : Nat) : Bit a x ↔ CompactMatrix.bit a x = true := by
  rw [CompactMatrix.bit_eq_testBit, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, q, r, he, hr⟩
    rw [pow2_iff] at hp
    subst p
    have hpos : 0 < 2^x := by positivity
    have he' : a = 2^x * (2*q+1) + r := by rw [he]; ring
    rw [he', Nat.mul_add_div hpos, Nat.div_eq_of_lt hr]
    omega
  · intro h
    refine ⟨2^x, (pow2_iff _ _).mpr rfl, a / 2^x / 2, a % 2^x, ?_,
      Nat.mod_lt _ (by positivity)⟩
    have hq := Nat.mod_add_div (a / 2^x) 2
    rw [h] at hq
    have ha := Nat.mod_add_div a (2^x)
    calc
      a = a % 2^x + 2^x * (a / 2^x) := ha.symm
      _ = a / 2^x / 2 * (2^x+2^x) + 2^x + a % 2^x := by
        conv_lhs => rw [← hq]
        ring

@[simp] theorem realize_bitFormula_exact (a x : Peano.Term) (ρ : Nat → Nat) :
    (bitFormula a x).Realize ρ ↔ CompactMatrix.bit (a.realize ρ) (x.realize ρ) = true :=
  (realize_bitFormula a x ρ).trans (bit_iff _ _)

/-- Every compact formula is admitted, not only the image of an arithmetic
embedding. Binding uses the same named-variable overwrite convention. -/
def translate : CompactMatrix.Formula → Peano.Formula
  | .truth => ⊤
  | .imp a b => (translate a).imp (translate b)
  | .member a b => bitFormula (v a) (v b)
  | .equal a b => (v a).equal (v b)
  | .all x f => FOL.allAt x (translate f)

theorem compact_update (ρ : Nat → Nat) (x a : Nat) :
    Function.update ρ x a = CompactMatrix.update ρ x a := by
  funext y
  simp [CompactMatrix.update, Function.update_apply]

/-- Full standard-model correspondence, for arbitrary open formulas and all
assignments, rather than only closed embedded arithmetic sentences. -/
theorem realize_translate (f : CompactMatrix.Formula) (ρ : Nat → Nat) :
    (translate f).Realize ρ ↔ f.Realize ρ := by
  induction f generalizing ρ with
  | truth => simp [translate, CompactMatrix.Formula.Realize]
  | imp a b ia ib => simp [translate, CompactMatrix.Formula.Realize, ia, ib]
  | member a b =>
    simpa [translate, v, CompactMatrix.Formula.Realize] using
      realize_bitFormula_exact (v a) (v b) ρ
  | equal a b => simp [translate, v, CompactMatrix.Formula.Realize]
  | all x f ih =>
    simp only [translate, FOL.realize_allAt, CompactMatrix.Formula.Realize]
    exact forall_congr' (fun a => by rw [compact_update]; exact ih _)

/-- Close the unbound compact names by the producer's actual zero assignment.
This is capture-avoiding term substitution in the canonical arithmetic syntax. -/
def toPA (code : Nat) : Peano.Sentence :=
  (translate (CompactMatrix.decode code)).subst
    (fun _ => (.func .zero Fin.elim0 : Peano.language.Term Empty))

/-- The compact-to-arithmetic standard-truth map is closed for every numeric
formula code. This theorem makes no object-level derivability assertion. -/
theorem truth_toPA (code : Nat) :
    (Nat ⊨ toPA code) ↔ (CompactMatrix.decode code).Realize (fun _ => 0) := by
  unfold toPA FirstOrder.Language.Sentence.Realize FirstOrder.Language.Formula.Realize
  rw [BoundedFormula.realize_subst]
  exact realize_translate _ _

/-- Free arithmetic term substitution into an interpreted compact formula has
exactly the corresponding assignment semantics. Bound names remain protected. -/
theorem realize_translate_subst (f : CompactMatrix.Formula)
    (σ : Nat → Peano.Term) (ρ : Nat → Nat) :
    FirstOrder.Language.Formula.Realize ((translate f).subst σ) ρ ↔
      f.Realize (fun x => (σ x).realize ρ) :=
  (FOL.realize_subst _ _ _).trans (realize_translate _ _)

/-- Renaming on the arithmetic side is the same change of free environment. -/
theorem realize_translate_rename (f : CompactMatrix.Formula)
    (r : Nat → Nat) (ρ : Nat → Nat) :
    ((translate f).relabel r).Realize ρ ↔ f.Realize (ρ ∘ r) :=
  (FOL.realize_rename _ _ _).trans (realize_translate _ _)

end PASoundness.CompactArithmetic
