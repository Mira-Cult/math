import PASoundness.PAtoCompactGraphAdjoinPreserve

/-! Literal K preservation of all original graph entries during one adjunction
step in the proposed multiplication-row construction. This is only an old-
graph inclusion lemma; it constructs neither the appended row nor a product. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldGraphPreserve
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactGraphAdjoinPreserve
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Every entry of the original graph 10 belongs to graph h. This is a
syntactic constructor; the theorem uses only fresh fixed graph labels 7/12. -/
def oldPreserved (h : Nat) : Formula := .all 9 (.imp (.member 10 9) (.member h 9))

def extension : Formula := namedAdjoin 7 13 12 14

private def point_step : KDerivation (imp extension.encode
    (imp (Formula.imp (.member 10 9) (.member 7 9)).encode
      (Formula.imp (.member 10 9) (.member 12 9)).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 10 9, imp (member 10 9) (member 7 9), extension.encode]
  have hm : Context Γ (member 10 9) := .head _ _
  have hi : Context Γ (imp (member 10 9) (member 7 9)) := .hypothesis (by simp [Γ])
  have he : Context Γ extension.encode := .hypothesis (by simp [Γ])
  have he' : Context Γ (adjoinCode 7 13 12 14) := by
    simpa [extension, namedAdjoin, PAtoCompactZeroSuccessor.namedBoth,
      PAtoCompactZeroSuccessor.namedEither, Formula.encode, adjoinCode,
      both, neg, either] using he
  exact .mp (.mp hm hi) (.mp he' (.closed (adjoin_preserves_row 7 13 12 14 9
    (by decide) (by decide) (by decide) (by decide))))

/-- The original graph remains included in the extended graph. -/
def old_preserved_step : KDerivation (imp extension.encode
    (imp (oldPreserved 7).encode (oldPreserved 12).encode)) := by
  have hv : KDerivation (imp extension.encode (allCode 9 extension.encode)) :=
    extension.vacuity 9 (by decide)
  exact conditionalAllCongr 9 hv point_step

theorem old_preserved_step_certificate : theoremCode (certificate old_preserved_step) =
    imp extension.encode (imp (oldPreserved 7).encode (oldPreserved 12).encode) :=
  certificate_correct old_preserved_step
end PASoundness.PAtoCompactMultiplicationOldGraphPreserve
#print axioms PASoundness.PAtoCompactMultiplicationOldGraphPreserve.old_preserved_step
#print axioms PASoundness.PAtoCompactMultiplicationOldGraphPreserve.old_preserved_step_certificate
