import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactOrderIsomorphism

/-! The right conjunct of the exact quotient-candidate bijection matrix,
conditional on equal input names, diagonal coverage and a supplied uniform
graph-equality theorem. This is finite K proof data; it does not establish the
premises, graph existence, quotient reflexivity, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalBijectionRight
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def coverage : Nat := allCode 2 (imp (member 0 2) (graphFormula 6 2 2).encode)
def uniformEquality : Nat := allCode 28 (allCode 29
  (imp (graphFormula 6 28 29).encode (equal 28 29)))

def uniqueBody : Formula := .all 4 (.imp
  (namedBoth (.member 0 4) (graphFormula 6 4 3)) (.equal 4 2))

def witnessBody : Formula := namedBoth (.member 0 2)
  (namedBoth (graphFormula 6 2 3) uniqueBody)

def rightClause : Formula := .all 3 (.imp (.member 1 3) (.ex 2 witnessBody))

/-- The companion clause, named only to expose the exact matrix split. -/
def leftClause : Formula := .all 2 (.imp (.member 0 2) (.ex 3
  (namedBoth (.member 1 3) (namedBoth (graphFormula 6 2 3)
    (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3)))))))

/-- The two clauses are exactly the existing candidate bijection formula. -/
theorem bijection_alignment : bijectionFormula = namedBoth leftClause rightClause := rfl

/-- Uniform graph-equality instance at the fresh test name 4 and target 3. -/
def uniform_instance : KDerivation (imp uniformEquality
    (imp (graphFormula 6 4 3).encode (equal 4 3))) := by
  let f : Formula := .imp (graphFormula 6 28 29) (.equal 28 29)
  have h28 := CompactNamed.universalInstance 28 4 (.all 29 f) (by decide)
    (by decide) (by decide)
  have h28r : CompactNamed.replace 28 4 (.all 29 f) =
      .all 29 (.imp (graphFormula 6 4 29) (.equal 4 29)) := by decide
  rw [h28r] at h28
  have h28' : KDerivation (imp uniformEquality
      (allCode 29 (imp (graphFormula 6 4 29).encode (equal 4 29)))) := by
    simpa [uniformEquality, f, Formula.encode] using h28
  let g : Formula := .imp (graphFormula 6 4 29) (.equal 4 29)
  have h29 := CompactNamed.universalInstance 29 3 g (by decide) (by decide) (by decide)
  have h29r : CompactNamed.replace 29 3 g = .imp (graphFormula 6 4 3) (.equal 4 3) := by decide
  rw [h29r] at h29
  have h29' : KDerivation (imp (allCode 29 (imp (graphFormula 6 4 29).encode (equal 4 29)))
      (imp (graphFormula 6 4 3).encode (equal 4 3))) := by simpa [g, Formula.encode] using h29
  exact compose h28' h29'

/-- Coverage instantiated at the target name 3. -/
def coverage_instance : KDerivation (imp coverage
    (imp (member 0 3) (graphFormula 6 3 3).encode)) := by
  let f : Formula := .imp (.member 0 2) (graphFormula 6 2 2)
  have h := CompactNamed.universalInstance 2 3 f (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 2 3 f = .imp (.member 0 3) (graphFormula 6 3 3) := by decide
  rw [hr] at h
  simpa [coverage, f, Formula.encode] using h

/-- Pointwise uniqueness of the diagonal preimage, generalized over name 4. -/
def uniqueness : KDerivation (imp uniformEquality
    (allCode 4 (imp (both (member 0 4) (graphFormula 6 4 3).encode) (equal 4 3)))) := by
  let H := uniformEquality
  let W := both (member 0 4) (graphFormula 6 4 3).encode
  have hpoint : KDerivation (imp H (imp W (equal 4 3))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [W,H]
    have hw : Context Γ W := Context.head _ _
    have hh : Context Γ H := .hypothesis (by simp [Γ])
    exact .mp (Context.conjunctionRight hw) (.mp hh (.closed uniform_instance))
  let fH : Formula := .all 28 (.all 29 (.imp (graphFormula 6 28 29) (.equal 28 29)))
  have hv : KDerivation (imp H (allCode 4 H)) := by
    have h := fH.vacuity 4 (by decide)
    simpa [fH,H,uniformEquality,Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [H] (imp W (equal 4 3)) := .mp (Context.head [] H) (.closed hpoint)
  exact Context.generalize 4 (by
    intro z hz
    have he : z = H := by simpa using hz
    cases he
    exact hv) hp

/-- Conditional derivation of the exact right-bijection clause. -/
def right_clause : KDerivation (imp (equal 0 1) (imp coverage
    (imp uniformEquality rightClause.encode))) := by
  let EQ := equal 0 1
  let C := coverage
  let H := uniformEquality
  let E := (Formula.ex 2 witnessBody).encode
  let M := member 1 3
  let Γ := [H,C,EQ]
  have hlocal : Context Γ (imp M E) := by
    apply Context.deduction
    have hm : Context (M :: Γ) M := Context.head Γ M
    have he : Context (M :: Γ) EQ := .hypothesis (by simp [Γ])
    have hc : Context (M :: Γ) C := .hypothesis (by simp [Γ])
    have hh : Context (M :: Γ) H := .hypothesis (by simp [Γ])
    have hm0 : Context (M :: Γ) (member 0 3) :=
      .mp hm (.mp (Context.eqSymm he) (.closed (memberLeftEquality 1 0 3)))
    have hg : Context (M :: Γ) (graphFormula 6 3 3).encode :=
      .mp hm0 (.mp hc (.closed coverage_instance))
    have hu : Context (M :: Γ) (allCode 4
        (imp (both (member 0 4) (graphFormula 6 4 3).encode) (equal 4 3))) :=
      .mp hh (.closed uniqueness)
    have hw : Context (M :: Γ) (both (member 0 3)
        (both (graphFormula 6 3 3).encode (allCode 4
          (imp (both (member 0 4) (graphFormula 6 4 3).encode) (equal 4 3))))) :=
      Context.conjunctionIntro hm0 (Context.conjunctionIntro hg hu)
    have hi := exists_variable_intro 2 3 witnessBody (by decide) (by decide) (by decide)
    let f : Formula := namedBoth (.member 0 3) (namedBoth (graphFormula 6 3 3)
      (.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 6 4 3)) (.equal 4 3))))
    have hrAst : CompactNamed.replace 2 3 witnessBody = f := by decide
    have hr : (CompactNamed.replace 2 3 witnessBody).encode =
        both (member 0 3) (both (graphFormula 6 3 3).encode (allCode 4
          (imp (both (member 0 4) (graphFormula 6 4 3).encode) (equal 4 3)))) := by
      rw [hrAst]
      rfl
    rw [hr] at hi
    exact .mp hw (.closed hi)
  have hvEQ : KDerivation (imp EQ (allCode 3 EQ)) := equalityVacuity 0 1 3 (by decide) (by decide)
  let fC : Formula := .all 2 (.imp (.member 0 2) (graphFormula 6 2 2))
  have hvC : KDerivation (imp C (allCode 3 C)) := by
    have h := fC.vacuity 3 (by decide)
    simpa [fC,C,coverage,Formula.encode] using h
  let fH : Formula := .all 28 (.all 29 (.imp (graphFormula 6 28 29) (.equal 28 29)))
  have hvH : KDerivation (imp H (allCode 3 H)) := by
    have h := fH.vacuity 3 (by decide)
    simpa [fH,H,uniformEquality,Formula.encode] using h
  have hall : Context Γ (allCode 3 (imp M E)) := Context.generalize 3 (by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases h1 : z = H
    · subst z; exact hvH
    · by_cases h2 : z = C
      · subst z; exact hvC
      · have h3 : z = EQ := (hz.resolve_left h1).resolve_left h2
        subst z; exact hvEQ) hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem right_clause_certificate : theoremCode (certificate right_clause) =
    imp (equal 0 1) (imp coverage (imp uniformEquality rightClause.encode)) :=
  certificate_correct right_clause

end PASoundness.PAtoCompactDiagonalBijectionRight

#print axioms PASoundness.PAtoCompactDiagonalBijectionRight.right_clause
#print axioms PASoundness.PAtoCompactDiagonalBijectionRight.right_clause_certificate
