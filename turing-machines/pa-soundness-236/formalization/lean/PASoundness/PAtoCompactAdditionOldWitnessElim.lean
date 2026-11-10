import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactAdditionSuffixAlignment

/-! Finite K elimination of the two original addition witnesses. A caller
supplies a literal K continuation from all four old cut/suffix facts to an
arbitrary target. The remaining assumptions and target must have no free
occurrences of 33 or 34; bound occurrences are allowed and handled by
capture-safe K vacuity. This is a proof constructor, not a successor-step,
addition-totality, or PA-soundness theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldWitnessElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactAdditionSuffixAlignment
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The literal four cut/suffix facts under the two existential binders in
`additionFormula`. -/
def oldBody : Formula := namedBoth (namedEither (.equal 33 32) (.member 32 33))
  (namedBoth (equivAt 30 33) (namedBoth suffixFormula (equivAt 31 34)))

theorem addition_body_shape : additionFormula = .ex 33 (.ex 34 oldBody) := by rfl

theorem oldBody_code : oldBody.encode =
    both (either (equal 33 32) (member 32 33))
      (both (equivAt 30 33).encode
        (both (filterGraph 32 34 35 (neg (member 33 35))) (equivAt 31 34).encode)) := by rfl

/-- A finite K continuation from the four literal witness facts extends to the
original addition formula. Free-name side conditions prevent capture when
eliminating both witnesses; the target and premise may bind these names. -/
def eliminate_old_witnesses (P G : Formula)
    (hp33 : 33 ∉ P.free) (hp34 : 34 ∉ P.free)
    (hg33 : 33 ∉ G.free) (hg34 : 34 ∉ G.free)
    (point : KDerivation (imp P.encode
      (imp (either (equal 33 32) (member 32 33))
        (imp (equivAt 30 33).encode
          (imp (filterGraph 32 34 35 (neg (member 33 35)))
            (imp (equivAt 31 34).encode G.encode)))))) :
    KDerivation (imp P.encode (imp additionFormula.encode G.encode)) := by
  let X := existsCode 34 oldBody.encode
  let Γ := [P.encode]
  have hp : Context Γ P.encode := .head _ _
  have hbody : Context Γ (imp oldBody.encode G.encode) := by
    apply Context.deduction
    have hb : Context (oldBody.encode :: Γ) oldBody.encode := .head _ _
    have hp' : Context (oldBody.encode :: Γ) P.encode := .under hp _
    rw [oldBody_code] at hb
    have hc := Context.conjunctionLeft hb
    have he := Context.conjunctionLeft (Context.conjunctionRight hb)
    have hf := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hb))
    have hlast := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hb))
    exact .mp hlast (.mp hf (.mp he (.mp hc (.mp hp' (.closed point)))))
  have hv34 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 34 h)) := by
    intro h hh
    have he : h = P.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 34 P hp34
  have hv33 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 33 h)) := by
    intro h hh
    have he : h = P.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 33 P hp33
  have hall34 : Context Γ (allCode 34 (imp oldBody.encode G.encode)) :=
    Context.generalize 34 hv34 hbody
  have hinner : Context Γ (imp X G.encode) := by
    apply Context.deduction
    exact Context.existsElim (free_vacuity 34 G hg34) (.under hall34 _) (.head _ _)
  have hall33 : Context Γ (allCode 33 (imp X G.encode)) :=
    Context.generalize 33 hv33 hinner
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hresult : Context [additionFormula.encode,P.encode] G.encode := by
    apply Context.existsElim (free_vacuity 33 G hg33) (.under hall33 _)
    simpa [addition_body_shape,Formula.encode,X] using
      (Context.head [P.encode] additionFormula.encode)
  exact hresult

theorem eliminate_old_witnesses_certificate (P G : Formula)
    (hp33 : 33 ∉ P.free) (hp34 : 34 ∉ P.free)
    (hg33 : 33 ∉ G.free) (hg34 : 34 ∉ G.free)
    (point : KDerivation (imp P.encode
      (imp (either (equal 33 32) (member 32 33))
        (imp (equivAt 30 33).encode
          (imp (filterGraph 32 34 35 (neg (member 33 35)))
            (imp (equivAt 31 34).encode G.encode)))))) :
    theoremCode (certificate (eliminate_old_witnesses P G hp33 hp34 hg33 hg34 point)) =
      imp P.encode (imp additionFormula.encode G.encode) :=
  certificate_correct (eliminate_old_witnesses P G hp33 hp34 hg33 hg34 point)
end PASoundness.PAtoCompactAdditionOldWitnessElim
#print axioms PASoundness.PAtoCompactAdditionOldWitnessElim.addition_body_shape
#print axioms PASoundness.PAtoCompactAdditionOldWitnessElim.oldBody_code
#print axioms PASoundness.PAtoCompactAdditionOldWitnessElim.eliminate_old_witnesses
#print axioms PASoundness.PAtoCompactAdditionOldWitnessElim.eliminate_old_witnesses_certificate
