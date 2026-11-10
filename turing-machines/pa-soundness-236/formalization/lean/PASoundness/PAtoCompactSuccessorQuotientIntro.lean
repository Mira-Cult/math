import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactAlphaMapOne
import PASoundness.PAtoCompactMapNamesCongr
import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactCandidateDynamicReflexivity
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactGuardElimination PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactZeroSuccessor
/-! Literal named quotient-successor decomposition and capture-safe witness
introduction. These are finite K proof data; successor existence itself is not
claimed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorQuotientIntro
private theorem d0 (b x y : Nat) : mapNames (twoMap b 0 1 x y) (domainTemplate 0) = domainAt b x := by
  unfold domainAt
  apply mapNames_congr
  intro z hz
  have hnot : 1 ∉ (domainTemplate 0).names := by decide
  by_cases h0 : z = 0
  · subst z; simp [twoMap, oneMap]
  · have h1 : z ≠ 1 := by intro h; subst z; exact hnot hz
    simp [twoMap, oneMap, h0, h1]
private theorem d1 (b x y : Nat) : mapNames (twoMap b 0 1 x y) (domainTemplate 1) = domainAt b y := by
  have hh : domainTemplate 1 = mapNames (rename 0 1) (domainTemplate 0) := by decide
  rw [hh, mapNames_compose]
  unfold domainAt
  apply mapNames_congr
  intro z hz
  have hnot : 1 ∉ (domainTemplate 0).names := by decide
  by_cases h0 : z = 0
  · subst z; simp [Function.comp_apply, rename, twoMap, oneMap]
  · have h1 : z ≠ 1 := by intro h; subst z; exact hnot hz
    simp [Function.comp_apply, rename, twoMap, oneMap, h0, h1]
private theorem d7 (b x y : Nat) : mapNames (twoMap b 0 1 x y) (domainTemplate 7) = domainAt b (b+9) := by
  have hh : domainTemplate 7 = mapNames (rename 0 7) (domainTemplate 0) := by decide
  rw [hh, mapNames_compose]
  unfold domainAt
  apply mapNames_congr
  intro z hz
  have hnot : 1 ∉ (domainTemplate 0).names := by decide
  by_cases h0 : z = 0
  · subst z; simp [Function.comp_apply, rename, twoMap, oneMap, Nat.add_assoc]
  · have h1 : z ≠ 1 := by intro h; subst z; exact hnot hz
    simp [Function.comp_apply, rename, twoMap, oneMap, h0, h1]
private theorem er (b x y : Nat) : mapNames (twoMap b 0 1 x y) (replace 0 7 equivalentFormula) = equivAt b (b+9) y := by
  rw [← map_eq_replace 0 7 equivalentFormula (by decide), mapNames_compose]
  unfold equivAt
  have hn : normalizeBottom equivalentFormula = equivalentFormula := by decide
  rw [hn]
  apply mapNames_congr
  intro z hz
  simp only [Function.comp_apply]
  by_cases h0 : z = 0
  · subst z; simp [rename, twoMap, Nat.add_assoc]
  · by_cases h1 : z = 1
    · subst z; simp [rename, twoMap]
    · simp [rename, twoMap, h0, h1]
private theorem raw (b x y : Nat) : mapNames (twoMap b 0 1 x y) (.all 8 (namedSuccessorBody 0 7 8)) =
    .all (b+10) (namedSuccessorBody x (b+9) (b+10)) := by
  simp [mapNames, namedSuccessorBody, namedBoth, namedEither, twoMap, Nat.add_assoc]
theorem succAt_shape (b x y : Nat) : succAt b x y = Formula.ex (b+9) (andF (domainAt b x)
  (andF (domainAt b y) (andF (domainAt b (b+9))
    (andF (Formula.all (b+10) (namedSuccessorBody x (b+9) (b+10))) (equivAt b (b+9) y))))) := by
  unfold succAt successorTemplate
  change Formula.ex (b+9) (mapNames (twoMap b 0 1 x y) (andF (domainTemplate 0)
    (andF (domainTemplate 1) (andF (domainTemplate 7)
      (andF (Formula.all 8 (namedSuccessorBody 0 7 8)) (replace 0 7 equivalentFormula)))))) = _
  rw [mapNames_andF, mapNames_andF, mapNames_andF, mapNames_andF]
  rw [d0, d1, d7, raw, er]
end PASoundness.PAtoCompactSuccessorQuotientIntro

namespace PASoundness.PAtoCompactSuccessorQuotientIntro
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactAdjunction
open PASoundness.CompactProof

def succBody (b x y : Nat) : Formula :=
  andF (domainAt b x) (andF (domainAt b y) (andF (domainAt b (b+9))
    (andF (Formula.all (b+10) (namedSuccessorBody x (b+9) (b+10))) (equivAt b (b+9) y))))

theorem domain_witness_not_binder (b a : Nat) : b+9 ∉ (domainAt b a).binders := by
  unfold domainAt
  rw [mapNames_binders]
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hn : i ≠ 0 ∧ i ≠ 7 := by
    constructor
    · intro h; subst i; exact (by decide : 0 ∉ (domainTemplate 0).binders) hi
    · intro h; subst i; exact (by decide : 7 ∉ (domainTemplate 0).binders) hi
  simp [oneMap, hn.1] at he
  omega

theorem equiv_witness_not_binder (b a y : Nat) : b+9 ∉ (equivAt b a y).binders := by
  unfold equivAt
  rw [mapNames_binders]
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hn : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 7 := by
    constructor
    · intro h; subst i; exact (by decide : 0 ∉ (normalizeBottom equivalentFormula).binders) hi
    constructor
    · intro h; subst i; exact (by decide : 1 ∉ (normalizeBottom equivalentFormula).binders) hi
    · intro h; subst i; exact (by decide : 7 ∉ (normalizeBottom equivalentFormula).binders) hi
  simp [twoMap, hn.1, hn.2.1] at he
  omega

theorem domain_replace_witness (b a y : Nat) :
    replace (b+9) y (domainAt b a) = domainAt b (rename (b+9) y a) := by
  rw [← map_eq_replace (b+9) y _ (domain_witness_not_binder b a)]
  unfold domainAt
  rw [mapNames_compose]
  apply mapNames_congr
  intro i hi
  by_cases h0 : i = 0
  · subst i; simp [Function.comp_apply, oneMap]
  · have h7 : i ≠ 7 := by
      intro h; subst i; exact (by decide : 7 ∉ (domainTemplate 0).names) hi
    have hneq : b + 2 + i ≠ b+9 := by omega
    simp [Function.comp_apply, oneMap, h0, rename, hneq]

theorem equiv_replace_witness (b a c y : Nat) :
    replace (b+9) y (equivAt b a c) =
      equivAt b (rename (b+9) y a) (rename (b+9) y c) := by
  rw [← map_eq_replace (b+9) y _ (equiv_witness_not_binder b a c)]
  unfold equivAt
  rw [mapNames_compose]
  apply mapNames_congr
  intro i hi
  by_cases h0 : i = 0
  · subst i; simp [Function.comp_apply, twoMap]
  · by_cases h1 : i = 1
    · subst i; simp [Function.comp_apply, twoMap]
    · have h7 : i ≠ 7 := by
        intro h; subst i; exact (by decide : 7 ∉ (normalizeBottom equivalentFormula).names) hi
      have hneq : b + 2 + i ≠ b+9 := by omega
      simp [Function.comp_apply, twoMap, h0, h1, rename, hneq]

theorem replace_andF (x y : Nat) (a b : Formula) :
    replace x y (andF a b) = andF (replace x y a) (replace x y b) := by
  simp [andF, Formula.not, replace]

theorem raw_replace_witness (b x y : Nat) (hx : x < b+2) :
    replace (b+9) y (Formula.all (b+10) (namedSuccessorBody x (b+9) (b+10))) =
      Formula.all (b+10) (namedSuccessorBody x y (b+10)) := by
  have hxw : x ≠ b+9 := by omega
  simp [replace, namedSuccessorBody, namedBoth, namedEither, rename, hxw]

theorem succBody_replace (b x y : Nat) (hx : x < b+2) (hy : y < b) :
    replace (b+9) y (succBody b x y) =
      andF (domainAt b x) (andF (domainAt b y) (andF (domainAt b y)
        (andF (Formula.all (b+10) (namedSuccessorBody x y (b+10))) (equivAt b y y)))) := by
  unfold succBody
  rw [replace_andF, replace_andF, replace_andF, replace_andF]
  rw [domain_replace_witness, domain_replace_witness, domain_replace_witness,
    raw_replace_witness b x y hx, equiv_replace_witness]
  simp [rename, show x ≠ b+9 by omega, show y ≠ b+9 by omega]

end PASoundness.PAtoCompactSuccessorQuotientIntro

namespace PASoundness.PAtoCompactSuccessorQuotientIntro
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactAdjunction
open PASoundness.CompactProof

theorem raw_binders (b x y : Nat) :
    (Formula.all (b+10) (namedSuccessorBody x y (b+10))).binders = {b+10} := by
  simp [Formula.binders, namedSuccessorBody, namedBoth, namedEither]

theorem succBody_witness_unbound (b x y : Nat) : b+9 ∉ (succBody b x y).binders := by
  simp only [succBody, andF_binders, Finset.mem_union, not_or]
  refine ⟨domain_witness_not_binder b x, domain_witness_not_binder b y,
    domain_witness_not_binder b (b+9), ?_, equiv_witness_not_binder b (b+9) y⟩
  rw [raw_binders]
  simp

theorem succBody_output_unbound (b x y : Nat) (hy : y < b) : y ∉ (succBody b x y).binders := by
  have hd (a : Nat) : y ∉ (domainAt b a).binders := by
    intro h
    have hh := domainAt_private b a y h
    omega
  have he : y ∉ (equivAt b (b+9) y).binders := by
    intro h
    have hh := equivAt_private b (b+9) y y h
    omega
  simp only [succBody, andF_binders, Finset.mem_union, not_or]
  refine ⟨hd x, hd y, hd (b+9), ?_, he⟩
  rw [raw_binders]
  simp
  omega

/-- Instantiated candidate guards, a raw successor and reflexivity of its
output suffice to introduce the exact quotient-successor witness. -/
def quotient_successor_intro (b x y : Nat) (hx : x < b+2) (hy : y < b) :
    KDerivation (imp
      (andF (domainAt b x) (andF (domainAt b y) (andF (domainAt b y)
        (andF (Formula.all (b+10) (namedSuccessorBody x y (b+10))) (equivAt b y y))))).encode
      (succAt b x y).encode) := by
  have h := exists_variable_intro (b+9) y (succBody b x y) (by omega)
    (succBody_witness_unbound b x y) (succBody_output_unbound b x y hy)
  rw [succBody_replace b x y hx hy] at h
  simpa only [succAt_shape, succBody, Formula.encode] using h

end PASoundness.PAtoCompactSuccessorQuotientIntro

namespace PASoundness.PAtoCompactSuccessorQuotientIntro
open PASoundness.PAtoCompactCandidateDynamicReflexivity
open PASoundness.PAtoCompactAdjunction PASoundness.CompactProof PASoundness.CompactDerivations

theorem raw_successor_encode (b x y : Nat) :
    (Formula.all (b+10) (namedSuccessorBody x y (b+10))).encode =
      successorCode x y (b+10) := by rfl

/-- Exact pointwise K packaging from a raw successor and two candidate
conditions; output equivalence reflexivity is constructed internally. -/
def quotient_successor_of_raw (b x y : Nat) (hx : x < b+2) (hy : y < b) :
    KDerivation (imp (domainAt b x).encode (imp (successorCode x y (b+10))
      (imp (domainAt b y).encode (succAt b x y).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt b y).encode, successorCode x y (b+10), (domainAt b x).encode]
  have hd0 : Context Γ (domainAt b x).encode := .hypothesis (by simp [Γ])
  have hd1 : Context Γ (domainAt b y).encode := .hypothesis (by simp [Γ])
  have hr : Context Γ (successorCode x y (b+10)) := .hypothesis (by simp [Γ])
  have he : Context Γ (equivAt b y y).encode :=
    .mp hd1 (.closed (dynamic_reflexive b y (by omega)))
  have hraw : Context Γ (Formula.all (b+10) (namedSuccessorBody x y (b+10))).encode := by
    simpa only [raw_successor_encode] using hr
  have hpair := Context.conjunctionIntro hraw he
  have hpair' : Context Γ (andF (Formula.all (b+10) (namedSuccessorBody x y (b+10))) (equivAt b y y)).encode := by
    simpa [andF, Formula.not, Formula.encode, both, neg] using hpair
  have h2 := Context.conjunctionIntro hd1 hpair'
  have h2' : Context Γ (andF (domainAt b y) (andF (Formula.all (b+10)
      (namedSuccessorBody x y (b+10))) (equivAt b y y))).encode := by
    simpa [andF, Formula.not, Formula.encode, both, neg] using h2
  have h3 := Context.conjunctionIntro hd1 h2'
  have h3' : Context Γ (andF (domainAt b y) (andF (domainAt b y)
      (andF (Formula.all (b+10) (namedSuccessorBody x y (b+10))) (equivAt b y y)))).encode := by
    simpa [andF, Formula.not, Formula.encode, both, neg] using h3
  have h4 := Context.conjunctionIntro hd0 h3'
  have h4' : Context Γ (andF (domainAt b x) (andF (domainAt b y) (andF (domainAt b y)
      (andF (Formula.all (b+10) (namedSuccessorBody x y (b+10))) (equivAt b y y))))).encode := by
    simpa [andF, Formula.not, Formula.encode, both, neg] using h4
  exact .mp h4' (.closed (quotient_successor_intro b x y hx hy))

end PASoundness.PAtoCompactSuccessorQuotientIntro

namespace PASoundness.PAtoCompactSuccessorQuotientIntro
open PASoundness.CompactProof PASoundness.PAtoCompactZeroSuccessor

theorem quotient_successor_intro_certificate (b x y : Nat) (hx : x < b+2) (hy : y < b) :
    theoremCode (certificate (quotient_successor_intro b x y hx hy)) =
      imp (andF (domainAt b x) (andF (domainAt b y) (andF (domainAt b y)
        (andF (Formula.all (b+10) (namedSuccessorBody x y (b+10))) (equivAt b y y))))).encode
        (succAt b x y).encode := certificate_correct _

theorem quotient_successor_of_raw_certificate (b x y : Nat) (hx : x < b+2) (hy : y < b) :
    theoremCode (certificate (quotient_successor_of_raw b x y hx hy)) =
      imp (domainAt b x).encode (imp (successorCode x y (b+10))
        (imp (domainAt b y).encode (succAt b x y).encode)) := certificate_correct _

end PASoundness.PAtoCompactSuccessorQuotientIntro

#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.succAt_shape
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.succBody
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.domain_witness_not_binder
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.equiv_witness_not_binder
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.domain_replace_witness
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.equiv_replace_witness
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.replace_andF
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.raw_replace_witness
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.succBody_replace
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.raw_binders
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.succBody_witness_unbound
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.succBody_output_unbound
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.quotient_successor_intro
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.raw_successor_encode
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.quotient_successor_of_raw
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.quotient_successor_intro_certificate
#print axioms PASoundness.PAtoCompactSuccessorQuotientIntro.quotient_successor_of_raw_certificate
