import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactAdjunction

/-! Assemble the literal fixed-binder Kuratowski formula from supplied graphs
whose two intermediate objects use fresh temporary names 23 and 24. It does
not construct those graphs or a quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactKuratowskiTemporary
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism

def singletonAt (a s : Nat) : CompactNamed.Formula :=
  .all 22 (namedBoth (.imp (.member s 22) (.equal 22 a))
    (.imp (.equal 22 a) (.member s 22)))
def pairAt (a b s : Nat) : CompactNamed.Formula :=
  .all 22 (namedBoth (.imp (.member s 22) (namedEither (.equal 22 a) (.equal 22 b)))
    (.imp (namedEither (.equal 22 a) (.equal 22 b)) (.member s 22)))

/-- The supplied graphs entail the target formula. The stated conditions
prevent replacing free endpoint/output names; interpreting all three graphs
as intended also requires their names to avoid the relevant bound labels. -/
def assemble_temporary (p a b : Nat)
    (hp20 : p ≠ 20) (hp21 : p ≠ 21)
    (ha20 : a ≠ 20) (ha21 : a ≠ 21)
    (hb20 : b ≠ 20) (hb21 : b ≠ 21) :
    KDerivation (imp (singletonAt a 23).encode (imp (pairAt a b 24).encode
      (imp (pairAt 23 24 p).encode (pairFormula p a b).encode))) := by
  let A := singletonAt a 23
  let B := pairAt a b 24
  let C := pairAt 23 24 p
  let F := namedBoth A (namedBoth B C)
  let F21 := namedBoth A (namedBoth (pairAt a b 21) (pairAt 23 21 p))
  let F20 := CompactNamed.Formula.ex 21
    (namedBoth (singletonAt a 20) (namedBoth (pairAt a b 21) (pairAt 20 21 p)))
  let Γ := [C.encode,B.encode,A.encode]
  have ha : Context Γ A.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ B.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ C.encode := .hypothesis (by simp [Γ])
  have hconj : Context Γ F.encode := Context.conjunctionIntro ha (Context.conjunctionIntro hb hc)
  have hi21 := exists_variable_intro 21 24 F21 (by decide)
    (by simp [F21,A,singletonAt,pairAt,namedBoth,namedEither,CompactNamed.Formula.binders])
    (by simp [F21,A,singletonAt,pairAt,namedBoth,namedEither,CompactNamed.Formula.binders])
  have hF21 : (CompactNamed.replace 21 24 F21).encode = F.encode := by
    simp [F21,F,A,B,C,singletonAt,pairAt,namedBoth,namedEither,CompactNamed.replace,
      CompactNamed.rename,CompactNamed.Formula.encode,hp21,ha21,hb21]
  rw [hF21] at hi21
  have h21 : Context Γ (CompactNamed.Formula.ex 21 F21).encode := .mp hconj (.closed hi21)
  have hi20 := exists_variable_intro 20 23 F20 (by decide)
    (by simp [F20,singletonAt,pairAt,namedBoth,namedEither,CompactNamed.Formula.binders])
    (by simp [F20,singletonAt,pairAt,namedBoth,namedEither,CompactNamed.Formula.binders])
  have hF20 : (CompactNamed.replace 20 23 F20).encode =
      (CompactNamed.Formula.ex 21 F21).encode := by
    simp [F20,F21,A,singletonAt,pairAt,namedBoth,namedEither,CompactNamed.replace,
      CompactNamed.rename,CompactNamed.Formula.encode,hp20,ha20,hb20]
  rw [hF20] at hi20
  have h20 : Context Γ (CompactNamed.Formula.ex 20 F20).encode := .mp h21 (.closed hi20)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  change Context Γ (CompactNamed.Formula.ex 20 F20).encode
  exact h20

theorem assemble_temporary_certificate (p a b : Nat)
    (hp20 : p ≠ 20) (hp21 : p ≠ 21)
    (ha20 : a ≠ 20) (ha21 : a ≠ 21)
    (hb20 : b ≠ 20) (hb21 : b ≠ 21) :
    theoremCode (certificate (assemble_temporary p a b hp20 hp21 ha20 ha21 hb20 hb21)) =
      imp (singletonAt a 23).encode (imp (pairAt a b 24).encode
        (imp (pairAt 23 24 p).encode (pairFormula p a b).encode)) :=
  certificate_correct (assemble_temporary p a b hp20 hp21 ha20 ha21 hb20 hb21)

end PASoundness.PAtoCompactKuratowskiTemporary

#print axioms PASoundness.PAtoCompactKuratowskiTemporary.assemble_temporary
#print axioms PASoundness.PAtoCompactKuratowskiTemporary.assemble_temporary_certificate
