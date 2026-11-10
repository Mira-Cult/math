import PASoundness.PAtoCompactAdditionOldSourceWitness

/-! Extract an old-source witness from the old bijection and transfer it to
the unequal-top extension. This establishes only the old-source point case
under the displayed graph hypotheses, not full bijection or totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldSourceClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldSourceWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldBijection : Formula := replace 1 34 (replace 0 31 bijectionFormula)
def oldLeft : Formula := .all 2 (.imp (.member 31 2) (.ex 3 oldBody))
def oldRight : Formula := match oldBijection with
  | .imp (.imp _ (.imp r .bottom)) .bottom => r
  | _ => .truth

theorem old_bijection_shape : oldBijection.encode = both oldLeft.encode oldRight.encode := by
  have h : oldBijection = namedBoth oldLeft oldRight := by decide
  simpa [namedBoth,Formula.not,Formula.encode,both,neg] using congrArg Formula.encode h

/-- The old bijection's first conjunct supplies an old witness for each old
source at the displayed point 2. -/
def old_witness : KDerivation (imp oldBijection.encode (imp (member 31 2)
    (existsCode 3 oldBody.encode))) := by
  let f : Formula := .imp (.member 31 2) (.ex 3 oldBody)
  have hinst := allSpecialize 2 f (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 2,oldBijection.encode]
  have hb : Context Γ oldBijection.encode := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 31 2) := .head _ _
  rw [old_bijection_shape] at hb
  have hl : Context Γ (allCode 2 f.encode) := Context.conjunctionLeft hb
  exact .mp hx (.mp hl (.closed hinst))

/-- Every displayed old source obtains a unique target in the extended graph
and suffix, using the supplied old bijection and clean-graph and adjunction
data. -/
def old_source_case : KDerivation (imp oldBijection.encode (imp oldClean.encode
    (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp (adjoinCode 34 32 40 41) (imp (member 31 2)
        (existsCode 3 newBody.encode))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 2,adjoinCode 34 32 40 41,(pairFormula 11 31 32).encode,
    adjoinCode 6 11 9 16,oldClean.encode,oldBijection.encode]
  have hm : Context Γ (member 31 2) := .head _ _
  have hs : Context Γ (adjoinCode 34 32 40 41) := .hypothesis (by simp [Γ])
  have hp : Context Γ (pairFormula 11 31 32).encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (adjoinCode 6 11 9 16) := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ oldBijection.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ (existsCode 3 oldBody.encode) := .mp hm (.mp hb (.closed old_witness))
  exact .mp ho (.mp hm (.mp hs (.mp hp (.mp ha (.mp hc (.closed transfer))))))

theorem old_source_case_certificate : theoremCode (certificate old_source_case) =
    imp oldBijection.encode (imp oldClean.encode (imp (adjoinCode 6 11 9 16)
      (imp (pairFormula 11 31 32).encode (imp (adjoinCode 34 32 40 41)
        (imp (member 31 2) (existsCode 3 newBody.encode)))))) :=
  certificate_correct old_source_case
end PASoundness.PAtoCompactAdditionOldSourceClosed
#print axioms PASoundness.PAtoCompactAdditionOldSourceClosed.old_witness
#print axioms PASoundness.PAtoCompactAdditionOldSourceClosed.old_source_case
#print axioms PASoundness.PAtoCompactAdditionOldSourceClosed.old_source_case_certificate
