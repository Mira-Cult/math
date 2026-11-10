import PASoundness.PAtoCompactFreshenCanonical
import PASoundness.PAtoCompactFreshenSingleAlpha

/-! A bounded syntactic alpha relation and canonical freshening. A common
allocation bound must cover intermediate formulas in a transitive chain. -/
namespace PASoundness.PAtoCompactFreshenAlphaRelation

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFreshenCanonical PASoundness.PAtoCompactFreshenSingleAlpha
open PASoundness.PAtoCompactFreshenReplace

def Bounded (start : Nat) (f : Formula) : Prop := ∀ v ∈ f.names, v < start

/-- Syntactic alpha changes and congruence; transitivity records a bound for
the intermediate formula, which need not follow from its endpoints. -/
inductive Alpha (start : Nat) : Formula → Formula → Prop
  | refl (a) : Alpha start a a
  | symm {a b} : Alpha start a b → Alpha start b a
  | trans {a b c} : Alpha start a b → Alpha start b c → Bounded start b → Alpha start a c
  | imp {a a' b b'} : Alpha start a a' → Alpha start b b' → Alpha start (.imp a b) (.imp a' b')
  | all {a b} (x) : Alpha start a b → Alpha start (.all x a) (.all x b)
  | ex {a b} (x) : Alpha start a b → Alpha start (.ex x a) (.ex x b)
  | allAlpha (x y) (a) : x ∉ a.binders → y ∉ a.names → Alpha start (.all x a) (.all y (replace x y a))
  | exAlpha (x y) (a) : x ∉ a.binders → y ∉ a.names → Alpha start (.ex x a) (.ex y (replace x y a))

theorem freshen_alpha {limit : Nat} {a b : Formula} (h : Alpha limit a b) :
    ∀ (start : Nat), limit ≤ start → ∀ (ha : Bounded start a) (hb : Bounded start b),
    (freshen a start ha).next = (freshen b start hb).next ∧
    (freshen a start ha).formula = (freshen b start hb).formula := by
  induction h with
  | refl a => intro start hs ha hb; exact ⟨rfl, rfl⟩
  | symm h ih =>
      intro start hs ha hb
      have hh := ih start hs hb ha
      exact ⟨hh.1.symm, hh.2.symm⟩
  | trans h₁ h₂ hm ih₁ ih₂ =>
      intro start hs ha hb
      have hm' : Bounded start _ := fun v hv => (hm v hv).trans_le hs
      have h₁' := ih₁ start hs ha hm'
      have h₂' := ih₂ start hs hm' hb
      exact ⟨h₁'.1.trans h₂'.1, h₁'.2.trans h₂'.2⟩
  | imp h₁ h₂ ih₁ ih₂ =>
      rename_i a a' b b'
      intro start hs ha hb
      let hla : Bounded start a := fun v hv => ha v (Finset.mem_union_left _ hv)
      let hla' : Bounded start a' := fun v hv => hb v (Finset.mem_union_left _ hv)
      let la := freshen a start hla
      let la' := freshen a' start hla'
      have hl := ih₁ start hs hla hla'
      have hnext : la.next = la'.next := hl.1
      let hrb : Bounded la.next b := fun v hv =>
        (ha v (Finset.mem_union_right _ hv)).trans_le la.next_ge
      let hrb' : Bounded la'.next b' := fun v hv =>
        (hb v (Finset.mem_union_right _ hv)).trans_le la'.next_ge
      have hbb' : Bounded la.next b' := by
        intro v hv
        rw [hnext]
        exact hrb' v hv
      have hr := ih₂ la.next (hs.trans la.next_ge) hrb hbb'
      have hstart := freshen_start_congr b' la.next la'.next hnext hbb' hrb'
      change (freshen b la.next hrb).next = (freshen b' la'.next hrb').next ∧
        Formula.imp la.formula (freshen b la.next hrb).formula =
          Formula.imp la'.formula (freshen b' la'.next hrb').formula
      exact ⟨hr.1.trans hstart.1, congrArg₂ Formula.imp hl.2 (hr.2.trans hstart.2)⟩
  | all x h ih =>
      rename_i a b
      intro start hs ha hb
      let hla : Bounded start a := fun v hv => ha v (Finset.mem_insert_of_mem hv)
      let hlb : Bounded start b := fun v hv => hb v (Finset.mem_insert_of_mem hv)
      have hh := ih start hs hla hlb
      change (freshen a start hla).next + 1 = (freshen b start hlb).next + 1 ∧
        Formula.all (freshen a start hla).next (replace x (freshen a start hla).next (freshen a start hla).formula) =
          Formula.all (freshen b start hlb).next (replace x (freshen b start hlb).next (freshen b start hlb).formula)
      rw [hh.1, hh.2]
      exact ⟨rfl, rfl⟩
  | ex x h ih =>
      rename_i a b
      intro start hs ha hb
      let hla : Bounded start a := fun v hv => ha v (Finset.mem_insert_of_mem hv)
      let hlb : Bounded start b := fun v hv => hb v (Finset.mem_insert_of_mem hv)
      have hh := ih start hs hla hlb
      change (freshen a start hla).next + 1 = (freshen b start hlb).next + 1 ∧
        Formula.ex (freshen a start hla).next (replace x (freshen a start hla).next (freshen a start hla).formula) =
          Formula.ex (freshen b start hlb).next (replace x (freshen b start hlb).next (freshen b start hlb).formula)
      rw [hh.1, hh.2]
      exact ⟨rfl, rfl⟩
  | allAlpha x y a hx hy =>
      intro start hs ha hb
      exact ⟨freshen_all_alpha_next x y a start hx hy ha hb, freshen_all_alpha x y a start hx hy ha hb⟩
  | exAlpha x y a hx hy =>
      intro start hs ha hb
      exact ⟨freshen_ex_alpha_next x y a start hx hy ha hb, freshen_ex_alpha x y a start hx hy ha hb⟩

/-- Bounded syntactic alpha changes yield actual finite K proof data in both
directions, by the common freshening. -/
def alphaProofEquiv {start : Nat} {a b : Formula} (h : Alpha start a b)
    (ha : Bounded start a) (hb : Bounded start b) : ProofEquiv a b :=
  commonFreshening a b start ha hb (freshen_alpha h start (le_refl _) ha hb).2

end PASoundness.PAtoCompactFreshenAlphaRelation

#print axioms PASoundness.PAtoCompactFreshenAlphaRelation.freshen_alpha
#print axioms PASoundness.PAtoCompactFreshenAlphaRelation.alphaProofEquiv
