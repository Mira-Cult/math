import PASoundness.PAtoCompactAdjunction

/-! Capture-safe introduction and elimination of a fresh endpoint alias in
literal K. The template connects a formula instantiated at old prefix 8 to
an existential name 12 explicitly equated to 8. It does not establish the
partial-inverse successor invariant, choose images, or construct graphs.
Compact code 1 remains the literal encoded bottom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPrefixAlias
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Attach explicit equality to the fresh endpoint alias. -/
def aliasBody (f : Formula) : Formula := namedBoth (.equal 12 8) f

/-- Any capture-safe formula instance at name 8 supplies a 12-witness
explicitly equal to 8, retaining the full uninstantiated formula. -/
def alias_intro (f : Formula) (h12 : 12 ∉ f.binders) (h8 : 8 ∉ f.binders) :
    KDerivation (imp (replace 12 8 f).encode (existsCode 12 (aliasBody f).encode)) := by
  have hi := exists_variable_intro 12 8 (aliasBody f) (by decide)
    (by simpa [aliasBody, namedBoth, Formula.not, Formula.binders] using h12)
    (by simpa [aliasBody, namedBoth, Formula.not, Formula.binders] using h8)
  have hbody : (replace 12 8 (aliasBody f)).encode =
      both (equal 8 8) (replace 12 8 f).encode := by
    simp [aliasBody, namedBoth, Formula.encode, replace, rename, both, neg]
  rw [hbody] at hi
  apply Context.closeEmpty
  apply Context.deduction
  let A := (replace 12 8 f).encode
  have ha : Context [A] A := Context.head [] A
  have he : Context [A] (equal 8 8) := .closed (equalityReflexive 8)
  exact .mp (Context.conjunctionIntro he ha) (.closed hi)

/-- If an alias-scoped K derivation proves a conclusion not mentioning name
12, eliminate the alias without assuming an equation between independent free
names 8 and 12. -/
def alias_elim (f result : Formula) (h12 : 12 ∉ f.binders) (h8 : 8 ∉ f.binders)
    (hresult : 12 ∉ result.names)
    (step : KDerivation (imp (aliasBody f).encode result.encode)) :
    KDerivation (imp (replace 12 8 f).encode result.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let A := (replace 12 8 f).encode
  let Γ := [A]
  have ha : Context Γ A := Context.head [] A
  have hex : Context Γ (existsCode 12 (aliasBody f).encode) :=
    .mp ha (.closed (alias_intro f h12 h8))
  have hall : Context Γ (allCode 12 (imp (aliasBody f).encode result.encode)) :=
    .closed (.generalize 12 step)
  exact Context.existsElim (result.vacuity 12 hresult) hall hex

theorem alias_intro_certificate (f : Formula) (h12 : 12 ∉ f.binders) (h8 : 8 ∉ f.binders) :
    theoremCode (certificate (alias_intro f h12 h8)) =
      imp (replace 12 8 f).encode (existsCode 12 (aliasBody f).encode) :=
  certificate_correct (alias_intro f h12 h8)

theorem alias_elim_certificate (f result : Formula) (h12 : 12 ∉ f.binders)
    (h8 : 8 ∉ f.binders) (hresult : 12 ∉ result.names)
    (step : KDerivation (imp (aliasBody f).encode result.encode)) :
    theoremCode (certificate (alias_elim f result h12 h8 hresult step)) =
      imp (replace 12 8 f).encode result.encode :=
  certificate_correct (alias_elim f result h12 h8 hresult step)

end PASoundness.PAtoCompactPrefixAlias

#print axioms PASoundness.PAtoCompactPrefixAlias.alias_intro
#print axioms PASoundness.PAtoCompactPrefixAlias.alias_elim
#print axioms PASoundness.PAtoCompactPrefixAlias.alias_intro_certificate
#print axioms PASoundness.PAtoCompactPrefixAlias.alias_elim_certificate
