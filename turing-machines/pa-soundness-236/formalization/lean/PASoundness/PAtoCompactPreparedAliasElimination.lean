import PASoundness.PAtoCompactEquivalentAliasInstantiation
import PASoundness.CompactQuantifiers

/-! K equality-guard elimination for the prepared order-isomorphism formula.
Both endpoint aliases are fresh bound names; the proof keeps the literal
compact code-one negation and makes no assertion of raw substitution semantics. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPreparedAliasElimination
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactRestrictedEquivalentTarget
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def conj (a b : Formula) : Formula := (a.imp b.not).not
def aliasFormula (x y : Nat) (f : Formula) : Formula := .ex x (conj (.equal x y) f)

/-- A bounded, syntactic K proof constructor. The additional fresh z
establishes vacuity of the *bound* alias formula via alpha conversion. -/
def alias_equiv (x y z : Nat) (f : Formula) (hxy : x ≠ y) (hxz : x ≠ z)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders)
    (hz : z ∉ (conj (.equal x y) f).names) :
    KDerivation (imp (aliasFormula x y f).encode (replace x y f).encode) ×
    KDerivation (imp (replace x y f).encode (aliasFormula x y f).encode) := by
  let body := conj (.equal x y) f
  let f' := replace x y f
  let alt : Formula := .ex z (replace x z body)
  have hxb : x ∉ body.binders := by simpa [body, conj, Formula.not, Formula.binders] using hx
  have ha := existentialAlpha x z body hxz hxb hz
  have hxalt : x ∉ alt.names := by
    have h := replace_avoids x z body hxz hxb
    simpa [alt, Formula.names, hxz] using h
  have hva : KDerivation (imp (aliasFormula x y f).encode (allCode x (aliasFormula x y f).encode)) := by
    have hv := alt.vacuity x hxalt
    exact compose ha.1 (compose hv (allCongr x ha.2))
  have hvf : KDerivation (imp f'.encode (allCode x f'.encode)) :=
    f'.vacuity x (replace_avoids x y f hxy hx)
  have hr := equalityReplace x y f hx hy
  have hi := existsIntroduce x body hxb
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    have hb : KDerivation (imp body.encode f'.encode) := by
      apply Context.closeEmpty
      apply Context.deduction
      have hbody := Context.head [] body.encode
      have he : Context [body.encode] (equal x y) := Context.conjunctionLeft hbody
      have hf : Context [body.encode] f.encode := Context.conjunctionRight hbody
      exact .mp hf (.mp he (.closed hr.1))
    exact Context.existsElim hvf (.closed (.generalize x hb)) (Context.head [] (aliasFormula x y f).encode)
  · apply Context.closeEmpty
    apply Context.deduction
    have hb : KDerivation (imp (equal x y) (imp f'.encode (aliasFormula x y f).encode)) := by
      apply Context.closeEmpty
      apply Context.deduction
      apply Context.deduction
      have he := Context.under (Context.head [] (equal x y)) f'.encode
      have hf' := Context.head [equal x y] f'.encode
      have hf : Context [f'.encode, equal x y] f.encode := .mp hf' (.mp he (.closed hr.2))
      have hc : Context [f'.encode, equal x y] body.encode := Context.conjunctionIntro he hf
      exact .mp hc (.closed hi)
    have hb' : KDerivation (imp f'.encode (imp (equal x y) (aliasFormula x y f).encode)) := by
      apply Context.closeEmpty
      apply Context.deduction
      apply Context.deduction
      exact .mp (Context.under (Context.head [] f'.encode) (equal x y))
        (.mp (Context.head [f'.encode] (equal x y)) (.closed hb))
    have himp : Context [f'.encode] (allCode x (imp (equal x y) (aliasFormula x y f).encode)) :=
      Context.allMP (.mp (Context.head [] f'.encode) (.closed hvf)) (.closed (.generalize x hb'))
    exact Context.existsElim hva himp (.closed (existsEqual x y))

/-- Exact nested equality-guard wrapper around the prepared formula. -/
def guardedPrepared : Formula := aliasFormula 40 2 (aliasFormula 41 5 preparedAliases)

/-- The two sequential alias eliminations end at the exact independently
named restricted endpoint target. Each side condition is checked concretely. -/
def prepared_alias_equiv :
    KDerivation (imp guardedPrepared.encode endpointTarget.encode) ×
    KDerivation (imp endpointTarget.encode guardedPrepared.encode) := by
  let mid := replace 41 5 preparedAliases
  have hi := alias_equiv 41 5 42 preparedAliases (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have ho := alias_equiv 40 2 43 mid (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have he : replace 40 2 mid = endpointTarget := by decide
  have liftForward := existsCongr 40
    (contrapose (implicationCongr (CompactHilbertBasis.identity (equal 40 2)) (contrapose hi.1)))
  have liftBackward := existsCongr 40
    (contrapose (implicationCongr (CompactHilbertBasis.identity (equal 40 2)) (contrapose hi.2)))
  have hf : KDerivation (imp guardedPrepared.encode (aliasFormula 40 2 mid).encode) := liftForward
  have hb : KDerivation (imp (aliasFormula 40 2 mid).encode guardedPrepared.encode) := liftBackward
  rw [he] at ho
  exact ⟨compose hf ho.1, compose ho.2 hb⟩

theorem forward_certificate : theoremCode (certificate prepared_alias_equiv.1) =
    imp guardedPrepared.encode endpointTarget.encode := certificate_correct prepared_alias_equiv.1

theorem backward_certificate : theoremCode (certificate prepared_alias_equiv.2) =
    imp endpointTarget.encode guardedPrepared.encode := certificate_correct prepared_alias_equiv.2

end PASoundness.PAtoCompactPreparedAliasElimination

#print axioms PASoundness.PAtoCompactPreparedAliasElimination.alias_equiv
#print axioms PASoundness.PAtoCompactPreparedAliasElimination.prepared_alias_equiv
#print axioms PASoundness.PAtoCompactPreparedAliasElimination.forward_certificate
#print axioms PASoundness.PAtoCompactPreparedAliasElimination.backward_certificate
