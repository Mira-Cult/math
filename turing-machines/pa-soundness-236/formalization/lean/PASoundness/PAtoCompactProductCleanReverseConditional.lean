import PASoundness.PAtoCompactProductCleanRetain
import PASoundness.CompactNamed

/-! A finite K transformation of the multiplication reverse clause under the
exact product filter. The filtered-to-old triple implication at the competing
coordinates is an explicit proof-data input; no semantic soundness, complete
matrix, or multiplication totality is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanReverseConditional
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactProductCleanRetain PASoundness.PAtoCompactMultiplicationCandidate
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Triple formula with an explicitly selected graph label. -/
def triple (g a b c : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 a b) (graphFormula g 18 c))

def competitor (g : Nat) : Formula := namedBoth (.member 0 7)
  (namedBoth (.member 1 8) (triple g 7 8 5))
def equalities : Formula := namedBoth (.equal 7 3) (.equal 8 4)
def uniqueBody (g : Nat) : Formula := .imp (competitor g) equalities
def unique (g : Nat) : Formula := .all 7 (.all 8 (uniqueBody g))
def witnessBody (g : Nat) : Formula := namedBoth (.member 0 3)
  (namedBoth (.member 1 4) (namedBoth (triple g 3 4 5) (unique g)))
def reverseAt (g : Nat) : Formula := .all 5 (.imp (.member 2 5) (.ex 3 (.ex 4 (witnessBody g))))

/-- The named source is exactly the literal product reverse clause. -/
theorem reverse_old : reverseAt 6 = reverseFormula := by rfl
/-- The named target is exactly the same clause with graph name replaced. -/
theorem reverse_new : reverseAt 54 = replace 6 54 reverseFormula := by decide

private def F : Nat := filterCode 54
private def namedF : Formula := .all 55 (namedFilterBody 6 54 55 (cleanPredicate 55))
private theorem namedF_code : namedF.encode = F := by rfl
private def H : Formula := namedBoth namedF (.member 2 5)
private theorem H_code : H.encode = both F (member 2 5) := by rfl

/-- Given pointwise reflection of filtered triples at competitor labels 7,8,5,
K transfers uniqueness from the old graph to the filtered graph. -/
def uniqueness_transfer
    (reflect : KDerivation (imp F (imp (triple 54 7 8 5).encode (triple 6 7 8 5).encode))) :
    KDerivation (imp F (imp (unique 6).encode (unique 54).encode)) := by
  have hpoint : KDerivation (imp F (imp (uniqueBody 6).encode (uniqueBody 54).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [(competitor 54).encode,(uniqueBody 6).encode,F]
    have hn : Context Γ (competitor 54).encode := .head _ _
    have ho : Context Γ (uniqueBody 6).encode := .hypothesis (by simp [Γ])
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    have h0 := Context.conjunctionLeft hn
    have h1 := Context.conjunctionLeft (Context.conjunctionRight hn)
    have ht := Context.conjunctionRight (Context.conjunctionRight hn)
    have htold : Context Γ (triple 6 7 8 5).encode := .mp ht (.mp hf (.closed reflect))
    have hc : Context Γ (competitor 6).encode := by
      simpa [competitor,namedBoth,Formula.encode,both,neg] using
        Context.conjunctionIntro h0 (Context.conjunctionIntro h1 htold)
    exact .mp hc ho
  have hf8 : KDerivation (imp F (allCode 8 F)) := by
    simpa only [namedF_code] using namedF.vacuity 8 (by decide)
  have hf7 : KDerivation (imp F (allCode 7 F)) := by
    simpa only [namedF_code] using namedF.vacuity 7 (by decide)
  have h8 := conditionalAllCongr 8 hf8 hpoint
  have h7 := conditionalAllCongr 7 hf7 h8
  simpa [unique, Formula.encode] using h7

/-- A finite K proof of the entire reverse-clause transfer, conditional only
on the displayed reflection of a filtered competitor triple. The valid old
witness triple is retained by the actual filter theorem. -/
def reverse_clause_of_reflection
    (reflect : KDerivation (imp F (imp (triple 54 7 8 5).encode (triple 6 7 8 5).encode))) :
    KDerivation (imp F (imp (reverseAt 6).encode (reverseAt 54).encode)) := by
  have hpoint : KDerivation (imp H.encode (imp (witnessBody 6).encode (witnessBody 54).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(witnessBody 6).encode,H.encode]
    have hw : Context Γ (witnessBody 6).encode := .head _ _
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have hf : Context Γ F := Context.conjunctionLeft hh
    have hz : Context Γ (member 2 5) := Context.conjunctionRight hh
    have hx : Context Γ (member 0 3) := Context.conjunctionLeft hw
    have hy : Context Γ (member 1 4) := Context.conjunctionLeft (Context.conjunctionRight hw)
    have ht : Context Γ (triple 6 3 4 5).encode := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hw))
    have hu : Context Γ (unique 6).encode := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hw))
    have hn : Context Γ (triple 54 3 4 5).encode := by
      have r := retain_triple
      change KDerivation (imp F (imp (member 0 3) (imp (member 1 4) (imp (member 2 5)
        (imp (triple 6 3 4 5).encode (triple 54 3 4 5).encode))))) at r
      exact .mp ht (.mp hz (.mp hy (.mp hx (.mp hf (.closed r)))))
    have hu' : Context Γ (unique 54).encode := .mp hu (.mp hf (.closed (uniqueness_transfer reflect)))
    simpa [Γ,witnessBody,namedBoth,Formula.encode,both,neg] using
      Context.conjunctionIntro hx (Context.conjunctionIntro hy (Context.conjunctionIntro hn hu'))
  have hH4 : KDerivation (imp H.encode (allCode 4 H.encode)) := H.vacuity 4 (by decide)
  have hH3 : KDerivation (imp H.encode (allCode 3 H.encode)) := H.vacuity 3 (by decide)
  have h4 := conditionalExistsCongr 4 hH4 hpoint
  have h3 := conditionalExistsCongr 3 hH3 h4
  have hinner : KDerivation (imp F (imp (imp (member 2 5) (existsCode 3 (existsCode 4 (witnessBody 6).encode)))
      (imp (member 2 5) (existsCode 3 (existsCode 4 (witnessBody 54).encode))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 2 5,imp (member 2 5) (existsCode 3 (existsCode 4 (witnessBody 6).encode)),F]
    have hz : Context Γ (member 2 5) := .head _ _
    have ha : Context Γ (imp (member 2 5) (existsCode 3 (existsCode 4 (witnessBody 6).encode))) := .hypothesis (by simp [Γ])
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    have hh : Context Γ H.encode := by simpa only [H_code] using Context.conjunctionIntro hf hz
    exact .mp (.mp hz ha) (.mp hh (.closed h3))
  have hf5 : KDerivation (imp F (allCode 5 F)) := by
    simpa only [namedF_code] using namedF.vacuity 5 (by decide)
  simpa [reverseAt, Formula.encode] using conditionalAllCongr 5 hf5 hinner

theorem reverse_clause_of_reflection_certificate
    (reflect : KDerivation (imp F (imp (triple 54 7 8 5).encode (triple 6 7 8 5).encode))) :
    theoremCode (certificate (reverse_clause_of_reflection reflect)) =
      imp F (imp (reverseAt 6).encode (reverseAt 54).encode) :=
  certificate_correct (reverse_clause_of_reflection reflect)
end PASoundness.PAtoCompactProductCleanReverseConditional
#print axioms PASoundness.PAtoCompactProductCleanReverseConditional.uniqueness_transfer
#print axioms PASoundness.PAtoCompactProductCleanReverseConditional.reverse_clause_of_reflection
#print axioms PASoundness.PAtoCompactProductCleanReverseConditional.reverse_clause_of_reflection_certificate
