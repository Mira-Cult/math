import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactTransitiveWitness

/-! K proof-construction wrapper for a represented inverse graph. The input is
an explicit pointwise K proof `A → I → C`; it is not constructed here. Given
that each graph satisfying A has some inverse graph satisfying I, the wrapper
transports an existential A-graph to an existential C-graph. This is not a
proof that inverse graphs exist. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactIsoTransportWrapper
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Build existential graph transport from a literal pointwise derivation.
The source graph name g is absent from C and the inverse graph name h is
absent from A. The remaining binder assumptions are explicit. -/
def transport_exists (g h : Nat) (A I C : Formula)
    (hgh : g ≠ h) (hA : h ∉ A.names) (hC : g ∉ C.names)
    (step : KDerivation (imp A.encode (imp I.encode C.encode))) :
    KDerivation (imp (allCode g (imp A.encode (existsCode h I.encode)))
      (imp (existsCode g A.encode) (existsCode h C.encode))) := by
  let D := existsCode h I.encode
  let E := existsCode h C.encode
  have hUnderA : KDerivation (imp A.encode (imp D E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [D,A.encode]
    have hA' : Context Γ A.encode := .hypothesis (by simp [Γ])
    have hlocal : Context Γ (imp I.encode C.encode) := .mp hA' (.closed step)
    have hv : ∀ q, q ∈ [A.encode] → KDerivation (imp q (allCode h q)) := by
      intro q hq
      have he : q = A.encode := by simpa using hq
      subst q
      exact A.vacuity h hA
    have hlocal' : Context [A.encode] (imp I.encode C.encode) :=
      .mp (Context.head [] A.encode) (.closed step)
    have hall : Context [A.encode] (allCode h (imp I.encode C.encode)) :=
      Context.generalize h hv hlocal'
    have hall' : Context Γ (allCode h (imp I.encode C.encode)) := Context.under hall D
    have hd : Context Γ D := Context.head _ _
    exact exists_map_context hall' hd
  have hcompose : KDerivation (imp (imp A.encode D) (imp A.encode E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A.encode,imp A.encode D]
    have ha : Context Γ A.encode := Context.head _ _
    have hi : Context Γ (imp A.encode D) := .hypothesis (by simp [Γ])
    exact .mp (.mp ha hi) (.mp ha (.closed hUnderA))
  have hvE : KDerivation (imp E (allCode g E)) := by
    have hf : g ∉ (Formula.ex h C).names := by
      simp [Formula.names, hgh, hC]
    have hv := (Formula.ex h C).vacuity g hf
    simpa [Formula.encode, E] using hv
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode g A.encode, allCode g (imp A.encode D)]
  have hsource : Context Γ (existsCode g A.encode) := Context.head _ _
  have hInv : Context Γ (allCode g (imp A.encode D)) := .hypothesis (by simp [Γ])
  have hall : Context Γ (allCode g (imp A.encode E)) :=
    Context.allMP hInv (.closed (.generalize g hcompose))
  exact Context.existsElim hvE hall hsource

theorem transport_exists_certificate (g h : Nat) (A I C : Formula)
    (hgh : g ≠ h) (hA : h ∉ A.names) (hC : g ∉ C.names)
    (step : KDerivation (imp A.encode (imp I.encode C.encode))) :
    theoremCode (certificate (transport_exists g h A I C hgh hA hC step)) =
      imp (allCode g (imp A.encode (existsCode h I.encode)))
        (imp (existsCode g A.encode) (existsCode h C.encode)) :=
  certificate_correct (transport_exists g h A I C hgh hA hC step)

end PASoundness.PAtoCompactIsoTransportWrapper

#print axioms PASoundness.PAtoCompactIsoTransportWrapper.transport_exists
#print axioms PASoundness.PAtoCompactIsoTransportWrapper.transport_exists_certificate
