import PASoundness.PAtoCompactLessRightWrapper
import PASoundness.PAtoCompactEquivalentAliasGuardLift
import PASoundness.PAtoCompactPreparedAliasElimination
import PASoundness.CompactFreshen

/-! Capture-safe relabeling of a hypothetical canonical segment-transport
proof. The input remains explicit K proof data; neither graph existence nor
segment transport is asserted. Whole-formula freshening prevents collision
with the canonical isomorphism formula's coordinate and graph binders. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLessRightSegmentAliases
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactPreparedAliasElimination
open PASoundness.PAtoCompactLessRightWrapper
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A named formula for the exact transitivity code, with the displayed labels. -/
def namedTrans (x p q : Nat) : Formula := .all p (.all q (transitiveBody x p q))

def bothNamed (a b : Formula) : Formula := (a.imp b.not).not

/-- Original quotient equality at endpoint aliases 40,41, guarded by their
actual values. The guarded endpoints themselves may coincide with binders of
`equivalentFormula`; they occur only in equality atoms outside that formula. -/
def guardAt (a b : Nat) : Formula := .ex 40 (bothNamed (.equal 40 a)
  (.ex 41 (bothNamed (.equal 41 b) originalAliases)))

theorem canonical_guard : guardAt 2 5 = guarded originalAliases := by rfl

def canonicalFormula : Formula := .imp (namedTrans 0 11 12)
  (.imp (namedTrans 1 16 18) (.imp (.member 0 2)
    (.imp equivalentFormula (.ex 5 (bothNamed (.member 1 5) (guardAt 2 5))))))

def renamedGuardedFormula : Formula := .imp (namedTrans 1 11 12)
  (.imp (namedTrans 8 16 18) (.imp (.member 1 7)
    (.imp E18 (.ex 9 (bothNamed (.member 8 9) (guardAt 7 9))))))

theorem canonical_names_lt : ∀ v ∈ canonicalFormula.names, v < 100 := by decide
theorem renamed_names_lt : ∀ v ∈ renamedGuardedFormula.names, v < 100 := by decide

def freshCanonical := freshen canonicalFormula 100 canonical_names_lt
def freshRenamed := freshen renamedGuardedFormula 100 renamed_names_lt

/-- Exact equality of the two independently alpha-standardized formulas.
The 5-to-9 existential witness conversion is included in this check. -/
theorem renamed_fresh_syntax :
    replace 2 7 (replace 0 1 (replace 1 8 freshCanonical.formula)) =
      freshRenamed.formula := by decide

/-- An assumed canonical finite K proof transforms into an actual K proof at
the wrapper's outer/input labels, retaining the endpoint equality guards. -/
def rename_guarded (d : KDerivation canonicalFormula.encode) :
    KDerivation renamedGuardedFormula.encode := by
  have hF : KDerivation freshCanonical.formula.encode := .mp d freshCanonical.equivalent.forward
  have h8 := universalInstance 1 8 freshCanonical.formula (by decide) (by decide) (by decide)
  have d8 : KDerivation (replace 1 8 freshCanonical.formula).encode := .mp (.generalize 1 hF) h8
  have h1 := universalInstance 0 1 (replace 1 8 freshCanonical.formula)
    (by decide) (by decide) (by decide)
  have d1 : KDerivation (replace 0 1 (replace 1 8 freshCanonical.formula)).encode :=
    .mp (.generalize 0 d8) h1
  have h7 := universalInstance 2 7 (replace 0 1 (replace 1 8 freshCanonical.formula))
    (by decide) (by decide) (by decide)
  have d7 : KDerivation (replace 2 7 (replace 0 1 (replace 1 8 freshCanonical.formula))).encode :=
    .mp (.generalize 2 d1) h7
  rw [renamed_fresh_syntax] at d7
  exact .mp d7 freshRenamed.equivalent.backward

theorem rename_guarded_certificate (d : KDerivation canonicalFormula.encode) :
    theoremCode (certificate (rename_guarded d)) = renamedGuardedFormula.encode :=
  certificate_correct (rename_guarded d)

/-- Both equality guards are eliminated by explicit K equality substitution. -/
def guarded_to_E79 : KDerivation (imp (guardAt 7 9).encode E79.encode) := by
  let mid := replace 41 9 originalAliases
  have hi := alias_equiv 41 9 42 originalAliases (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have ho := alias_equiv 40 7 43 mid (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have he : replace 40 7 mid = E79 := by decide
  have liftForward := existsCongr 40
    (contrapose (implicationCongr (CompactHilbertBasis.identity (equal 40 7)) (contrapose hi.1)))
  have hf : KDerivation (imp (guardAt 7 9).encode (aliasFormula 40 7 mid).encode) := liftForward
  rw [he] at ho
  exact compose hf ho.1

/-- The exact member-transport interface needed by the right-order wrapper,
conditional solely on the explicitly supplied canonical K derivation. -/
def wrapper_segment (d : KDerivation canonicalFormula.encode) :
    KDerivation (imp sourceTrans (imp targetTrans (imp (member 1 7)
      (imp E18.encode (existsCode 9 segmentBody9.encode))))) := by
  have hbody : KDerivation (imp (bothNamed (.member 8 9) (guardAt 7 9)).encode
      segmentBody9.encode) := by
    change KDerivation (imp (neg (imp (member 8 9) (neg (guardAt 7 9).encode)))
      (neg (imp (member 8 9) (neg E79.encode))))
    exact contrapose (implicationCongr (CompactHilbertBasis.identity (member 8 9))
      (contrapose guarded_to_E79))
  have hex := existsCongr 9 hbody
  have h := implicationCongr (CompactHilbertBasis.identity E18.encode) hex
  have h := implicationCongr (CompactHilbertBasis.identity (member 1 7)) h
  have h := implicationCongr (CompactHilbertBasis.identity targetTrans) h
  have h := implicationCongr (CompactHilbertBasis.identity sourceTrans) h
  exact .mp (rename_guarded d) h

theorem wrapper_segment_certificate (d : KDerivation canonicalFormula.encode) :
    theoremCode (certificate (wrapper_segment d)) =
      imp sourceTrans (imp targetTrans (imp (member 1 7)
        (imp E18.encode (existsCode 9 segmentBody9.encode)))) :=
  certificate_correct (wrapper_segment d)

end PASoundness.PAtoCompactLessRightSegmentAliases

#print axioms PASoundness.PAtoCompactLessRightSegmentAliases.rename_guarded
#print axioms PASoundness.PAtoCompactLessRightSegmentAliases.rename_guarded_certificate

#print axioms PASoundness.PAtoCompactLessRightSegmentAliases.wrapper_segment
#print axioms PASoundness.PAtoCompactLessRightSegmentAliases.wrapper_segment_certificate
