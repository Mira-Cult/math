import PASoundness.PAtoCompactAdditionOldSourceUnique
import PASoundness.PAtoCompactGraphAdjoinPreserve

/-! Transfer an existing old-source bijection witness to the new graph and
new suffix. All graph data and the old witness remain explicit assumptions;
this is not old witness existence, full bijection or addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldSourceWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactGraphAdjoinPreserve PASoundness.PAtoCompactAdditionOldSourceUnique
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldBody : Formula := namedBoth (.member 34 3) (namedBoth (graphFormula 6 2 3)
  (.all 4 (.imp (namedBoth (.member 34 4) (graphFormula 6 2 4)) (.equal 4 3))))
def newBody : Formula := namedBoth (.member 40 3) (namedBoth (graphFormula 9 2 3)
  (.all 4 (.imp (graphFormula 9 2 4) (.equal 4 3))))

/-- An old witness remains a witness in the extended graph and suffix,
with uniqueness against every new-graph target. -/
def transfer : KDerivation (imp oldClean.encode (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp (adjoinCode 34 32 40 41)
      (imp (member 31 2) (imp (existsCode 3 oldBody.encode) (existsCode 3 newBody.encode))))))) := by
  let C := oldClean.encode
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let S := adjoinCode 34 32 40 41
  let M := member 31 2
  let Γ := [M,S,P,A,C]
  let adjG : Formula := namedAdjoin 6 11 9 16
  let adjS : Formula := namedAdjoin 34 32 40 41
  have vacC : KDerivation (imp C (allCode 3 C)) := oldClean.vacuity 3 (by decide)
  have vacA : KDerivation (imp A (allCode 3 A)) := by
    have h := adjG.vacuity 3 (by decide)
    simpa [A,adjG,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h
  have vacS : KDerivation (imp S (allCode 3 S)) := by
    have h := adjS.vacuity 3 (by decide)
    simpa [S,adjS,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h
  have vacP : KDerivation (imp P (allCode 3 P)) := (pairFormula 11 31 32).vacuity 3 (by decide)
  have vacM : KDerivation (imp M (allCode 3 M)) := membershipVacuity 31 2 3 (by decide) (by decide)
  have hpoint : Context Γ (imp oldBody.encode newBody.encode) := by
    apply Context.deduction
    let Δ := oldBody.encode :: Γ
    have ho : Context Δ oldBody.encode := .head _ _
    have hm : Context Δ M := .hypothesis (by simp [Δ,Γ])
    have hs : Context Δ S := .hypothesis (by simp [Δ,Γ])
    have hp : Context Δ P := .hypothesis (by simp [Δ,Γ])
    have ha : Context Δ A := .hypothesis (by simp [Δ,Γ])
    have hc : Context Δ C := .hypothesis (by simp [Δ,Γ])
    change Context Δ (both (member 34 3) (both (graphFormula 6 2 3).encode oldUnique)) at ho
    have ht : Context Δ (member 40 3) := .mp (Context.conjunctionLeft ho)
      (.mp hs (.closed (adjoin_preserves_row 34 32 40 41 3 (by decide) (by decide) (by decide) (by decide))))
    have hg : Context Δ (graphFormula 9 2 3).encode :=
      .mp (Context.conjunctionLeft (Context.conjunctionRight ho))
        (.mp ha (.closed (adjoin_preserves_edge 6 11 9 16 2 3
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))
    have hu : Context Δ oldUnique := Context.conjunctionRight (Context.conjunctionRight ho)
    have hn : Context Δ (allCode 4 (imp (graphFormula 9 2 4).encode (equal 4 3))) :=
      .mp hm (.mp hp (.mp ha (.mp hc (.mp hu (.closed competitor_unique_all)))))
    change Context Δ (both (member 40 3) (both (graphFormula 9 2 3).encode
      (allCode 4 (imp (graphFormula 9 2 4).encode (equal 4 3)))))
    exact Context.conjunctionIntro ht (Context.conjunctionIntro hg hn)
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases hm : z = M
    · subst z; exact vacM
    · by_cases hs : z = S
      · subst z; exact vacS
      · by_cases hp : z = P
        · subst z; exact vacP
        · by_cases ha : z = A
          · subst z; exact vacA
          · have hc : z = C := by simpa [hm,hs,hp,ha] using hz
            subst z; exact vacC
  have hall := Context.generalize 3 hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Ω := existsCode 3 oldBody.encode :: Γ
  have hex : Context Ω (existsCode 3 oldBody.encode) := .head _ _
  have hall' : Context Ω (allCode 3 (imp oldBody.encode newBody.encode)) :=
    Context.weaken hall (by intro z hz; exact List.mem_cons_of_mem _ hz)
  exact exists_map_context hall' hex

theorem transfer_certificate : theoremCode (certificate transfer) =
    imp oldClean.encode (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp (adjoinCode 34 32 40 41) (imp (member 31 2)
        (imp (existsCode 3 oldBody.encode) (existsCode 3 newBody.encode)))))) :=
  certificate_correct transfer
end PASoundness.PAtoCompactAdditionOldSourceWitness
#print axioms PASoundness.PAtoCompactAdditionOldSourceWitness.transfer
#print axioms PASoundness.PAtoCompactAdditionOldSourceWitness.transfer_certificate
