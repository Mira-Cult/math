import PASoundness.CompactDerivations
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Tauto
import PASoundness.RawMatrix

/-!
Auxiliary named syntax for constructive normalization of the exact compact
calculus. Logical bottom and existential binders are explicit nodes here,
and encode to the unchanged literal compact words 1 and `existsCode`.
This syntax is a proof-transformation IR, not a replacement PA definition.
-/
namespace PASoundness.CompactNamed

open CompactProof CompactHilbertBasis CompactDerivations
attribute [local irreducible] imp Cantor.pair Cantor.triangle

inductive Formula where
  | truth | bottom
  | imp (a b : Formula)
  | member (a b : Nat)
  | equal (a b : Nat)
  | all (x : Nat) (a : Formula)
  | ex (x : Nat) (a : Formula)
  deriving DecidableEq

namespace Formula

def encode : Formula → Nat
  | .truth => 0
  | .bottom => 1
  | .imp a b => CompactProof.imp a.encode b.encode
  | .member a b => CompactProof.member a b
  | .equal a b => CompactProof.equal a b
  | .all x a => allCode x a.encode
  | .ex x a => existsCode x a.encode

def not (a : Formula) : Formula := .imp a .bottom

def names : Formula → Finset Nat
  | .truth | .bottom => ∅
  | .imp a b => a.names ∪ b.names
  | .member a b | .equal a b => {a,b}
  | .all x a | .ex x a => insert x a.names

def binders : Formula → Finset Nat
  | .truth | .bottom | .member _ _ | .equal _ _ => ∅
  | .imp a b => a.binders ∪ b.binders
  | .all x a | .ex x a => insert x a.binders

def free : Formula → Finset Nat
  | .truth | .bottom => ∅
  | .imp a b => a.free ∪ b.free
  | .member a b | .equal a b => {a,b}
  | .all x a | .ex x a => a.free.erase x

theorem binders_subset_names (f : Formula) : f.binders ⊆ f.names := by
  induction f with
  | truth | bottom => exact Finset.Subset.refl _
  | member | equal => exact Finset.empty_subset _
  | imp a b ia ib => exact Finset.union_subset_union ia ib
  | all x f ih | ex x f ih => exact Finset.insert_subset_insert _ ih

theorem free_subset_names (f : Formula) : f.free ⊆ f.names := by
  induction f with
  | truth | bottom | member | equal => exact Finset.Subset.refl _
  | imp a b ia ib => exact Finset.union_subset_union ia ib
  | all x f ih | ex x f ih =>
    exact (Finset.erase_subset _ _).trans (ih.trans (Finset.subset_insert _ _))

theorem names_eq_free_union_binders (f : Formula) : f.names = f.free ∪ f.binders := by
  induction f with
  | truth | bottom | member | equal => simp [names, free, binders]
  | imp a b ia ib => simp [names, free, binders, ia, ib, Finset.union_assoc,
      Finset.union_left_comm, Finset.union_comm]
  | all x f ih | ex x f ih =>
    ext z
    simp only [names, free, binders, ih, Finset.mem_insert, Finset.mem_union,
      Finset.mem_erase]
    tauto

/-- The sole side condition is syntactic absence, including binder labels. -/
def vacuity (x : Nat) (f : Formula) (hx : x ∉ f.names) :
    KDerivation (CompactProof.imp f.encode (allCode x f.encode)) :=
  match f with
  | .truth => .mp (.generalize x .truth) (weakening (allCode x 0) 0)
  | .bottom => explosion (allCode x 1)
  | .imp a b => implicationVacuity x
      (vacuity x a (fun h => hx (Finset.mem_union_left _ h)))
      (vacuity x b (fun h => hx (Finset.mem_union_right _ h)))
  | .member a b => membershipVacuity a b x
      (fun h => hx (by simp [names, h])) (fun h => hx (by simp [names, h]))
  | .equal a b => equalityVacuity a b x
      (fun h => hx (by simp [names, h])) (fun h => hx (by simp [names, h]))
  | .all y a => universalVacuity x y
      (vacuity x a (fun h => hx (Finset.mem_insert_of_mem h)))
  | .ex y a => negationVacuity x (universalVacuity x y (negationVacuity x
      (vacuity x a (fun h => hx (Finset.mem_insert_of_mem h)))))

end Formula

/-- Exact bridge from every already decoded compact formula. -/
def ofDecoded : CompactMatrix.Formula → Formula
  | .truth => .truth
  | .imp a b => .imp (ofDecoded a) (ofDecoded b)
  | .member a b => .member a b
  | .equal a b => .equal a b
  | .all x a => .all x (ofDecoded a)

theorem encode_ofDecoded (f : CompactMatrix.Formula) :
    (ofDecoded f).encode = RawMatrix.encodeFormula f := by
  induction f <;> simp_all [ofDecoded, Formula.encode, RawMatrix.encodeFormula]

theorem encode_of_code (code : Nat) : (ofDecoded (CompactMatrix.decode code)).encode = code :=
  (encode_ofDecoded _).trans (RawMatrix.encode_decode code)

def rename (x y a : Nat) : Nat := if a = x then y else a

/-- Uniform replacement is used only when neither name is a binder. -/
def replace (x y : Nat) : Formula → Formula
  | .truth => .truth
  | .bottom => .bottom
  | .imp a b => .imp (replace x y a) (replace x y b)
  | .member a b => .member (rename x y a) (rename x y b)
  | .equal a b => .equal (rename x y a) (rename x y b)
  | .all z a => .all z (replace x y a)
  | .ex z a => .ex z (replace x y a)

theorem replace_binders (x y : Nat) (f : Formula) :
    (replace x y f).binders = f.binders := by
  induction f <;> simp_all [replace, Formula.binders]

theorem rename_avoids (x y a : Nat) (h : x ≠ y) : rename x y a ≠ x := by
  simp only [rename]
  split
  · exact Ne.symm h
  · assumption

theorem replace_avoids (x y : Nat) (f : Formula) (h : x ≠ y)
    (hb : x ∉ f.binders) : x ∉ (replace x y f).names := by
  induction f with
  | truth | bottom => simp [replace, Formula.names]
  | member a b | equal a b =>
    simp [replace, Formula.names, Ne.symm (rename_avoids x y a h),
      Ne.symm (rename_avoids x y b h)]
  | imp a b ia ib =>
    simp only [Formula.binders, Finset.mem_union, not_or] at hb
    simp [replace, Formula.names, ia hb.1, ib hb.2]
  | all z a ih | ex z a ih =>
    simp only [Formula.binders, Finset.mem_insert, not_or] at hb
    simp [replace, Formula.names, hb.1, ih hb.2]

theorem rename_roundtrip (x y a : Nat) (hy : y ≠ a) :
    rename y x (rename x y a) = a := by
  by_cases ha : a = x <;> simp [rename, ha, Ne.symm hy]

theorem replace_roundtrip (x y : Nat) (f : Formula) (hy : y ∉ f.names) :
    replace y x (replace x y f) = f := by
  induction f with
  | truth | bottom => rfl
  | member a b | equal a b =>
    simp only [Formula.names, Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    simp [replace, rename_roundtrip x y a hy.1, rename_roundtrip x y b hy.2]
  | imp a b ia ib =>
    simp only [Formula.names, Finset.mem_union, not_or] at hy
    simp [replace, ia hy.1, ib hy.2]
  | all z a ih | ex z a ih =>
    simp only [Formula.names, Finset.mem_insert, not_or] at hy
    simp [replace, ih hy.2]

def renameEquality {Γ : List Nat} {x y : Nat} (a : Nat)
    (h : Context Γ (equal x y)) : Context Γ (equal a (rename x y a)) := by
  by_cases he : a = x
  · subst a
    simpa only [rename, ↓reduceIte] using h
  · simpa only [rename, if_neg he] using Context.closed (Γ := Γ) (equalityReflexive a)

def memberReplace (x y a b : Nat) :
    KDerivation (imp (equal x y)
      (imp (member a b) (member (rename x y a) (rename x y b)))) ×
    KDerivation (imp (equal x y)
      (imp (member (rename x y a) (rename x y b)) (member a b))) := by
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have h := Context.under (Context.head [] (equal x y)) (member a b)
    exact Context.memCongr (renameEquality a h) (renameEquality b h)
      (Context.head [equal x y] (member a b))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have h := Context.under (Context.head [] (equal x y))
      (member (rename x y a) (rename x y b))
    exact Context.memCongr (Context.eqSymm (renameEquality a h))
      (Context.eqSymm (renameEquality b h))
      (Context.head [equal x y] (member (rename x y a) (rename x y b)))

def equalityReplaceAtom (x y a b : Nat) :
    KDerivation (imp (equal x y)
      (imp (equal a b) (equal (rename x y a) (rename x y b)))) ×
    KDerivation (imp (equal x y)
      (imp (equal (rename x y a) (rename x y b)) (equal a b))) := by
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have h := Context.under (Context.head [] (equal x y)) (equal a b)
    exact Context.eqCongr (renameEquality a h) (renameEquality b h)
      (Context.head [equal x y] (equal a b))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have h := Context.under (Context.head [] (equal x y))
      (equal (rename x y a) (rename x y b))
    exact Context.eqCongr (Context.eqSymm (renameEquality a h))
      (Context.eqSymm (renameEquality b h))
      (Context.head [equal x y] (equal (rename x y a) (rename x y b)))

def conditionalContrapose {e a b : Nat} (h : KDerivation (imp e (imp a b))) :
    KDerivation (imp e (imp (neg b) (neg a))) :=
  Context.closeEmpty (Context.deduction (Context.contrapose
    (.mp (Context.head [] e) (.closed h))))

def conditionalExistsCongr {e a b : Nat} (x : Nat)
    (hv : KDerivation (imp e (allCode x e)))
    (hi : KDerivation (imp e (imp a b))) :
    KDerivation (imp e (imp (existsCode x a) (existsCode x b))) :=
  conditionalContrapose (conditionalAllCongr x hv (conditionalContrapose hi))

/-- Bidirectional equality replacement expands entirely to K proof data. -/
def equalityReplace (x y : Nat) (f : Formula)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders) :
    KDerivation (imp (equal x y) (imp f.encode (replace x y f).encode)) ×
    KDerivation (imp (equal x y) (imp (replace x y f).encode f.encode)) :=
  match f with
  | .truth => ⟨.mp (identity 0) (weakening (imp 0 0) (equal x y)),
      .mp (identity 0) (weakening (imp 0 0) (equal x y))⟩
  | .bottom => ⟨.mp (identity 1) (weakening (imp 1 1) (equal x y)),
      .mp (identity 1) (weakening (imp 1 1) (equal x y))⟩
  | .member a b => memberReplace x y a b
  | .equal a b => equalityReplaceAtom x y a b
  | .imp a b =>
      let da := equalityReplace x y a
        (fun h => hx (Finset.mem_union_left _ h)) (fun h => hy (Finset.mem_union_left _ h))
      let db := equalityReplace x y b
        (fun h => hx (Finset.mem_union_right _ h)) (fun h => hy (Finset.mem_union_right _ h))
      ⟨conditionalImplicationCongr da.2 db.1, conditionalImplicationCongr da.1 db.2⟩
  | .all z a =>
      let d := equalityReplace x y a
        (fun h => hx (Finset.mem_insert_of_mem h)) (fun h => hy (Finset.mem_insert_of_mem h))
      let hv := equalityVacuity x y z
        (fun h => hx (by simp [Formula.binders, h]))
        (fun h => hy (by simp [Formula.binders, h]))
      ⟨conditionalAllCongr z hv d.1, conditionalAllCongr z hv d.2⟩
  | .ex z a =>
      let d := equalityReplace x y a
        (fun h => hx (Finset.mem_insert_of_mem h)) (fun h => hy (Finset.mem_insert_of_mem h))
      let hv := equalityVacuity x y z
        (fun h => hx (by simp [Formula.binders, h]))
        (fun h => hy (by simp [Formula.binders, h]))
      ⟨conditionalExistsCongr z hv d.1, conditionalExistsCongr z hv d.2⟩

/-- Actual instantiation at a distinct capture-safe variable. -/
def universalInstance (x y : Nat) (f : Formula) (hxy : x ≠ y)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders) :
    KDerivation (imp (allCode x f.encode) (replace x y f).encode) := by
  have hv := Formula.vacuity x (replace x y f) (replace_avoids x y f hxy hx)
  have hs := (equalityReplace x y f hx hy).1
  have hp : KDerivation (imp f.encode (imp (equal x y) (replace x y f).encode)) :=
    Context.closeEmpty (Context.deduction (Context.deduction
      (.mp (Context.under (Context.head [] f.encode) (equal x y))
        (.mp (Context.head [f.encode] (equal x y)) (.closed hs)))))
  exact Context.closeEmpty (Context.deduction (Context.existsElim hv
    (Context.allMP (Context.head [] (allCode x f.encode)) (.closed (.generalize x hp)))
    (.closed (existsEqual x y))))

/-- A one-assumption context can be generalized using a concrete vacuity proof. -/
def generalizeOne {a b : Nat} (x : Nat)
    (hv : KDerivation (imp a (allCode x a))) (d : Context [a] b) :
    Context [a] (allCode x b) :=
  Context.generalize x (fun h hm => by simpa only [List.mem_singleton.mp hm] using hv) d

/-- Alpha conversion requires absence of inner capture and produces both
literal compact implication derivations. -/
def universalAlpha (x y : Nat) (f : Formula) (hxy : x ≠ y)
    (hx : x ∉ f.binders) (hy : y ∉ f.names) :
    KDerivation (imp (allCode x f.encode) (allCode y (replace x y f).encode)) ×
    KDerivation (imp (allCode y (replace x y f).encode) (allCode x f.encode)) := by
  have hyb : y ∉ f.binders := fun h => hy (f.binders_subset_names h)
  have hxnames := replace_avoids x y f hxy hx
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    have hv := Formula.vacuity y (.all x f) (by
      simp only [Formula.names, Finset.mem_insert, not_or]
      exact ⟨Ne.symm hxy, hy⟩)
    exact generalizeOne y hv (.mp (Context.head [] (allCode x f.encode))
      (.closed (universalInstance x y f hxy hx hyb)))
  · have hi := universalInstance y x (replace x y f) (Ne.symm hxy)
      (by simpa only [replace_binders] using hyb)
      (by simpa only [replace_binders] using hx)
    rw [replace_roundtrip x y f hy] at hi
    apply Context.closeEmpty
    apply Context.deduction
    have hv := Formula.vacuity x (.all y (replace x y f)) (by
      simp only [Formula.names, Finset.mem_insert, not_or]
      exact ⟨hxy, hxnames⟩)
    exact generalizeOne x hv (.mp (Context.head [] (allCode y (replace x y f).encode))
      (.closed hi))

def existentialAlpha (x y : Nat) (f : Formula) (hxy : x ≠ y)
    (hx : x ∉ f.binders) (hy : y ∉ f.names) :
    KDerivation (imp (existsCode x f.encode) (existsCode y (replace x y f).encode)) ×
    KDerivation (imp (existsCode y (replace x y f).encode) (existsCode x f.encode)) := by
  have h := universalAlpha x y f.not hxy
    (by simpa [Formula.not, Formula.binders] using hx)
    (by simpa [Formula.not, Formula.names] using hy)
  exact ⟨contrapose h.2, contrapose h.1⟩

end PASoundness.CompactNamed
