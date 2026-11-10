import PASoundness.PAtoCompactProductCleanRetain
import PASoundness.PAtoCompactMultiplicationCandidate

/-! Assemble forward product-matrix preservation from the checked retained
edge theorem and an explicit K derivation transferring the universal
uniqueness clause. No semantic soundness or graph-existence result is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductForwardConditional
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactProductCleanRetain
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def triple9 (g : Nat) : Formula := replace 5 9 (tripleAt g)
def unique (g : Nat) : Formula := .all 9 (.imp (namedBoth (.member 2 9) (triple9 g)) (.equal 9 5))
def witnessBody (g : Nat) : Formula := namedBoth (.member 2 5)
  (namedBoth (tripleAt g) (unique g))
def witnessExists (g : Nat) : Formula := .ex 5 (witnessBody g)
def point4 (g : Nat) : Formula := .imp (.member 1 4) (witnessExists g)
def forall4 (g : Nat) : Formula := .all 4 (point4 g)
def point3 (g : Nat) : Formula := .imp (.member 0 3) (forall4 g)
def forwardAt (g : Nat) : Formula := .all 3 (point3 g)
private def filterNamed : Formula := .all 55 (namedFilterBody 6 54 55 (cleanPredicate 55))
private def e5 : Formula := namedBoth filterNamed (namedBoth (.member 0 3) (.member 1 4))
private def e4 : Formula := namedBoth filterNamed (.member 0 3)
private theorem filter_code : filterNamed.encode = filterCode 54 := rfl

/-- The new named clause is exactly the old product forward clause after
capture-safe replacement of graph label 6 by 54. -/
theorem forward_shape_old : forwardAt 6 = forwardFormula := by decide

theorem forward_shape_new : forwardAt 54 = replace 6 54 forwardFormula := by decide

/-- A K uniqueness-clause implication is the only remaining proof-data input.
All graph/endpoint restrictions occur as literal antecedents. -/
noncomputable def forward_from_uniqueness
    (hunique : KDerivation (imp (filterCode 54) (imp (unique 6).encode (unique 54).encode))) :
    KDerivation (imp (filterCode 54) (imp forwardFormula.encode (forwardAt 54).encode)) := by
  have hv5 : KDerivation (imp e5.encode (allCode 5 e5.encode)) := e5.vacuity 5 (by decide)
  have hbody : KDerivation (imp e5.encode (imp (witnessBody 6).encode (witnessBody 54).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(witnessBody 6).encode, e5.encode]
    have hb : Context Γ (witnessBody 6).encode := .head _ _
    have he : Context Γ e5.encode := .hypothesis (by simp [Γ])
    have hf : Context Γ (filterCode 54) := by
      simpa [e5,namedBoth,Formula.encode,both,neg,filter_code] using Context.conjunctionLeft he
    have hxy := Context.conjunctionRight he
    have hx : Context Γ (member 0 3) := Context.conjunctionLeft hxy
    have hy : Context Γ (member 1 4) := Context.conjunctionRight hxy
    have hz : Context Γ (member 2 5) := Context.conjunctionLeft hb
    have ht : Context Γ (tripleAt 6).encode := Context.conjunctionLeft (Context.conjunctionRight hb)
    have hu : Context Γ (unique 6).encode := Context.conjunctionRight (Context.conjunctionRight hb)
    have ht' : Context Γ (tripleAt 54).encode :=
      .mp ht (.mp hz (.mp hy (.mp hx (.mp hf (.closed retain_triple)))))
    have hu' : Context Γ (unique 54).encode := .mp hu (.mp hf (.closed hunique))
    change Context Γ (both (member 2 5) (both (tripleAt 54).encode (unique 54).encode))
    exact Context.conjunctionIntro hz (Context.conjunctionIntro ht' hu')
  have hex := conditionalExistsCongr 5 hv5 hbody
  have hv4 : KDerivation (imp e4.encode (allCode 4 e4.encode)) := e4.vacuity 4 (by decide)
  have hpoint4 : KDerivation (imp e4.encode (imp (point4 6).encode (point4 54).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 1 4,(point4 6).encode,e4.encode]
    have hy : Context Γ (member 1 4) := .head _ _
    have hp : Context Γ (point4 6).encode := .hypothesis (by simp [Γ])
    have he4 : Context Γ e4.encode := .hypothesis (by simp [Γ])
    have hf := Context.conjunctionLeft he4
    have hx := Context.conjunctionRight he4
    have he5 : Context Γ e5.encode := by
      simpa [e5,e4,namedBoth,Formula.encode,both,neg] using
        Context.conjunctionIntro hf (Context.conjunctionIntro hx hy)
    have ho : Context Γ (witnessExists 6).encode := .mp hy hp
    exact .mp ho (.mp he5 (.closed hex))
  have hall4 := conditionalAllCongr 4 hv4 hpoint4
  have hpoint3 : KDerivation (imp (filterCode 54) (imp (point3 6).encode (point3 54).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 0 3,(point3 6).encode,filterCode 54]
    have hx : Context Γ (member 0 3) := .head _ _
    have hp : Context Γ (point3 6).encode := .hypothesis (by simp [Γ])
    have hf : Context Γ (filterCode 54) := .hypothesis (by simp [Γ])
    have he4 : Context Γ e4.encode := by
      simpa [e4,namedBoth,Formula.encode,both,neg,filter_code] using Context.conjunctionIntro hf hx
    have ho : Context Γ (forall4 6).encode := .mp hx hp
    exact .mp ho (.mp he4 (.closed hall4))
  have hv3 : KDerivation (imp (filterCode 54) (allCode 3 (filterCode 54))) := by
    simpa only [filter_code] using filterNamed.vacuity 3 (by decide)
  have hall3 := conditionalAllCongr 3 hv3 hpoint3
  rw [← forward_shape_old]
  exact hall3

end PASoundness.PAtoCompactProductForwardConditional
#print axioms PASoundness.PAtoCompactProductForwardConditional.forward_from_uniqueness
