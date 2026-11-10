import PASoundness.PAtoCompactSuccRelationWitnessAlpha
import PASoundness.PAtoCompactDynamicTransitivityFinal
import PASoundness.PAtoCompactDynamicSymmetry
import PASoundness.PAtoCompactZeroGraphOutputTransport
import PASoundness.PAtoCompactSuccBaseMultiAlpha
import PASoundness.PAtoCompactFreeVacuity

/-! Finite K proof that quotient successor cannot be equivalent to zero. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccNeZeroDynamic
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSuccRelationWitnessAlpha PASoundness.PAtoCompactDynamicTransitivityFinal
open PASoundness.PAtoCompactDynamicSymmetry PASoundness.PAtoCompactZeroGraphOutputTransport
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactZeroBaseTransport PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactTemplateBlockShift
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A fresh witness version. The graph witness is eliminated inside K. -/
def not_zero_fresh (b x y z w : Nat)
    (hx : x < b+2) (hy : y < b+2) (hz : z < b+2) (hw : w < b+2)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    KDerivation (imp (succAt b x y).encode
      (imp (zeroAt b z).encode (imp (equivAt b y z).encode 1))) := by
  let G := andF (zeroAt b z) (equivAt b y z)
  have hGfree : w ∉ G.free := by
    intro h
    simp only [G, andF, Formula.not, Formula.free, Finset.union_empty, Finset.mem_union] at h
    rcases h with h | h
    · have hh := zeroAt_free b z h
      simp only [Finset.mem_singleton] at hh
      exact hwz hh
    · have hh := equivAt_free b y z h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh
      · exact hwy hh
      · exact hwz hh
  let M := matrix b x y w
  let raw := Formula.all (b+10) (namedSuccessorBody x w (b+10))
  have localProof : KDerivation (imp G.encode (imp M.encode 1)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode, G.encode]
    have hm : Context Γ M.encode := Context.head _ _
    have hg : Context Γ G.encode := .hypothesis (by simp [Γ])
    have hm' : Context Γ (both (domainAt b x).encode
      (both (domainAt b y).encode (both (domainAt b w).encode
        (both raw.encode (equivAt b w y).encode)))) := by
      simpa [M, matrix, raw, andF, Formula.not, Formula.encode, both, neg] using hm
    have hrest := Context.conjunctionRight (Context.conjunctionRight hm')
    have hdw : Context Γ (domainAt b w).encode := Context.conjunctionLeft hrest
    have htail := Context.conjunctionRight hrest
    have hraw : Context Γ (successorCode x w (b+10)) := by
      simpa [raw, Formula.encode, namedSuccessorBody, namedBoth, namedEither,
        successorCode, both, neg, either] using Context.conjunctionLeft htail
    have hewy : Context Γ (equivAt b w y).encode := Context.conjunctionRight htail
    have hg' : Context Γ (both (zeroAt b z).encode (equivAt b y z).encode) := by
      simpa [G, andF, Formula.not, Formula.encode, both, neg] using hg
    have hzero : Context Γ (zeroAt b z).encode := Context.conjunctionLeft hg'
    have heyz : Context Γ (equivAt b y z).encode := Context.conjunctionRight hg'
    have hewz : Context Γ (equivAt b w z).encode :=
      .mp heyz (.mp hewy (.mp hdw (.closed (dynamic_transitivity b w y z hw hy hz))))
    have hezw : Context Γ (equivAt b z w).encode :=
      .mp hewz (.mp hdw (.closed (dynamic_symmetry b w z hw hz)))
    have hzeroW : Context Γ (zeroAt b w).encode :=
      .mp hezw (.mp hzero (.closed (zero_output b z w hz hw)))
    have hzeroW' : Context Γ (zeroCode w (b+3)) := by
      simpa [zeroAt_shape, Formula.encode, zeroCode, neg] using hzeroW
    have hmember : Context Γ (member w x) :=
      .mp hraw (.closed (successor_contains_input x w (b+10) (by omega) (by omega)))
    exact .mp hmember (.mp hzeroW' (.closed (zero_excludes w (b+3) x (by omega) (by omega))))
  have hv := free_vacuity w G hGfree
  have helim : KDerivation (imp G.encode (imp (existsCode w M.encode) 1)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [existsCode w M.encode, G.encode]
    have he : Context Γ (existsCode w M.encode) := Context.head _ _
    have hpoint : Context [G.encode] (imp M.encode 1) :=
      .mp (Context.head [] G.encode) (.closed localProof)
    have hv' : ∀ h, h ∈ [G.encode] → KDerivation (imp h (allCode w h)) := by
      intro h hh
      have heq : h = G.encode := List.mem_singleton.mp hh
      subst h
      exact hv
    have hall : Context [G.encode] (allCode w (imp M.encode 1)) :=
      Context.generalize w hv' hpoint
    exact Context.existsElim (explosion (allCode w 1)) (Context.under hall (existsCode w M.encode)) he
  have hs := (rename_witness b x y w hx hy hw hwx hwy).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := (succAt b x y).encode
  let Z := (zeroAt b z).encode
  let E := (equivAt b y z).encode
  let Γ := [E,Z,S]
  have hs' : Context Γ S := .hypothesis (by simp [Γ])
  have hz' : Context Γ Z := .hypothesis (by simp [Γ])
  have he' : Context Γ E := Context.head _ _
  have hg : Context Γ G.encode := by
    simpa [G, andF, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hz' he'
  have hex : Context Γ (existsCode w M.encode) := .mp hs' (.closed hs)
  exact .mp hex (.mp hg (.closed helim))

/-- Quotient successor and zero cannot have equivalent outputs. Labels may
alias, provided they lie below the private allocation block. -/
def succ_not_equiv_zero (b x y z : Nat) (hx : x < b+2) (hy : y < b+2) (hz : z < b+2) :
    KDerivation (imp (succAt b x y).encode
      (imp (zeroAt b z).encode (imp (equivAt b y z).encode 1))) := by
  let w := max (max x y) z + 1
  let c := max b w + 1
  have hwx : w ≠ x := by dsimp [w]; omega
  have hwy : w ≠ y := by dsimp [w]; omega
  have hwz : w ≠ z := by dsimp [w]; omega
  have hxc : x < c+2 := by dsimp [c,w]; omega
  have hyc : y < c+2 := by dsimp [c,w]; omega
  have hzc : z < c+2 := by dsimp [c,w]; omega
  have hwc : w < c+2 := by dsimp [c,w]; omega
  have hf := not_zero_fresh c x y z w hxc hyc hzc hwc hwx hwy hwz
  have hs := (succAt_base_alpha b c x y hx hy hxc hyc).forward
  have hz' := zeroAt_base_forward b c z (by omega) (by omega)
  have he := (equivAt_base_alpha b c y z hy hz hyc hzc).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := (succAt b x y).encode
  let Z := (zeroAt b z).encode
  let E := (equivAt b y z).encode
  let Γ := [E,Z,S]
  have hS : Context Γ S := .hypothesis (by simp [Γ])
  have hZ : Context Γ Z := .hypothesis (by simp [Γ])
  have hE : Context Γ E := Context.head _ _
  exact .mp (.mp hE (.closed he)) (.mp (.mp hZ (.closed hz')) (.mp (.mp hS (.closed hs)) (.closed hf)))

end PASoundness.PAtoCompactSuccNeZeroDynamic
#print axioms PASoundness.PAtoCompactSuccNeZeroDynamic.succ_not_equiv_zero
