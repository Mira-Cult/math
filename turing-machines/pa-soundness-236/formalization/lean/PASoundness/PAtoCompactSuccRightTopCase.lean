import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactAdjunction

/-! Conditional top-target case for successor bijection. The exact edge split
and clean-old-edge endpoint extraction are supplied K proof data. Every graph,
new pair, irreflexivity and endpoint-equality premise is explicit. This file
does not establish graph collection, full congruence or PA translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccRightTopCase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactSuccCongruenceData
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldEdge : Nat := (graphFormula 6 4 28).encode
def newEdge : Nat := (graphFormula 9 4 28).encode
def addedCoordinates : Nat := both (equal 4 0) (equal 28 1)
def uniqueBody : Formula := .all 4 (.imp
  (namedBoth (.member 7 4) (graphFormula 9 4 28)) (.equal 4 2))
def witnessBody : Formula := namedBoth (.member 7 2)
  (namedBoth (graphFormula 9 2 28) uniqueBody)

/-- At the top target, every competing new edge has source 0. The split and
old-edge target endpoint are literal proof-data premises, not semantic facts. -/
def top_point
    (hSplit : KDerivation (imp newGraph (imp newPair (imp newEdge (either oldEdge addedCoordinates)))))
    (hClean : KDerivation (imp cleanGraph (imp oldEdge (member 1 28)))) :
    KDerivation (imp newGraph (imp newPair (imp cleanGraph (imp targetIrreflexive
      (imp (equal 28 1) (imp newEdge (equal 4 0))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [newEdge,equal 28 1,targetIrreflexive,cleanGraph,newPair,newGraph]
  have hg : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hp : Context Γ newPair := .hypothesis (by simp [Γ])
  have hc : Context Γ cleanGraph := .hypothesis (by simp [Γ])
  have hi : Context Γ targetIrreflexive := .hypothesis (by simp [Γ])
  have he : Context Γ (equal 28 1) := .hypothesis (by simp [Γ])
  have hn : Context Γ newEdge := Context.head _ _
  have hcases : Context Γ (either oldEdge addedCoordinates) :=
    .mp hn (.mp hp (.mp hg (.closed hSplit)))
  apply Context.disjunctionElim hcases
  · let A := oldEdge
    have ha : Context (A :: Γ) A := Context.head Γ A
    have hc' : Context (A :: Γ) cleanGraph := Context.under hc A
    have he' : Context (A :: Γ) (equal 28 1) := Context.under he A
    have hi' : Context (A :: Γ) targetIrreflexive := Context.under hi A
    have hm : Context (A :: Γ) (member 1 28) := .mp ha (.mp hc' (.closed hClean))
    have hs : Context (A :: Γ) (member 1 1) :=
      .mp he' (.mp hm (.closed (memberRightEquality 1 28 1)))
    exact Context.explode (equal 4 0) (.mp hs hi')
  · have ha : Context (addedCoordinates :: Γ) addedCoordinates := Context.head Γ _
    exact Context.conjunctionLeft ha

/-- Conditional pointwise top-case derivation, now generalized over every
competing source name 4, retaining the literal source-successor guard. -/
def top_unique
    (hSplit : KDerivation (imp newGraph (imp newPair (imp newEdge (either oldEdge addedCoordinates)))))
    (hClean : KDerivation (imp cleanGraph (imp oldEdge (member 1 28)))) :
    KDerivation (imp newGraph (imp newPair (imp cleanGraph (imp targetIrreflexive
      (imp (equal 28 1) (allCode 4 (imp (both (member 7 4) newEdge) (equal 4 0)))))))) := by
  let A := newGraph
  let B := newPair
  let C := cleanGraph
  let D := targetIrreflexive
  let T := equal 28 1
  let Γ := [T,D,C,B,A]
  have hlocal : Context Γ (imp (both (member 7 4) newEdge) (equal 4 0)) := by
    apply Context.deduction
    let Δ := both (member 7 4) newEdge :: Γ
    have hx : Context Δ (both (member 7 4) newEdge) := Context.head Γ _
    have hA : Context Δ A := .hypothesis (by simp [Δ,Γ])
    have hB : Context Δ B := .hypothesis (by simp [Δ,Γ])
    have hC : Context Δ C := .hypothesis (by simp [Δ,Γ])
    have hD : Context Δ D := .hypothesis (by simp [Δ,Γ])
    have hT : Context Δ T := .hypothesis (by simp [Δ,Γ])
    exact .mp (Context.conjunctionRight hx) (.mp hT (.mp hD (.mp hC (.mp hB (.mp hA (.closed (top_point hSplit hClean)))))))
  let fA : Formula := namedAdjoin 6 11 9 16
  let fB : Formula := pairFormula 11 0 1
  let fC : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 0 1))
  let fD : Formula := .imp (.member 1 1) .bottom
  let fT : Formula := .equal 28 1
  have hvA : KDerivation (imp A (allCode 4 A)) := by
    have h := fA.vacuity 4 (by decide)
    simpa [A,newGraph,fA,namedAdjoin,adjoinCode,namedBoth,namedEither,
      Formula.encode,both,neg,either] using h
  have hvB : KDerivation (imp B (allCode 4 B)) := fB.vacuity 4 (by decide)
  have hvC : KDerivation (imp C (allCode 4 C)) := fC.vacuity 4 (by decide)
  have hvD : KDerivation (imp D (allCode 4 D)) := fD.vacuity 4 (by decide)
  have hvT : KDerivation (imp T (allCode 4 T)) := fT.vacuity 4 (by decide)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = T
    · subst h; exact hvT
    · by_cases hd : h = D
      · subst h; exact hvD
      · by_cases hc : h = C
        · subst h; exact hvC
        · by_cases hb : h = B
          · subst h; exact hvB
          · have ha : h = A := by simpa [he,hd,hc,hb] using hh
            subst h; exact hvA
  have hAll := Context.generalize 4 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hAll

/-- The supplied adjunction has the new pair object as an element. -/
def adjoin_contains_new_pair : KDerivation (imp newGraph (member 9 11)) := by
  let f := namedBoth (.imp (.member 9 16) (namedEither (.equal 16 11) (.member 6 16)))
    (.imp (namedEither (.equal 16 11) (.member 6 16)) (.member 9 16))
  have hi := universalInstance 16 11 f (by decide)
    (by simp [f,namedBoth,namedEither,Formula.binders])
    (by simp [f,namedBoth,namedEither,Formula.binders])
  have hi' : KDerivation (imp newGraph
      (both (imp (member 9 11) (either (equal 11 11) (member 6 11)))
        (imp (either (equal 11 11) (member 6 11)) (member 9 11)))) := by
    simpa [f,newGraph,namedBoth,namedEither,adjoinCode,Formula.encode,replace,rename,
      both,neg,either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  have hg : Context [newGraph] newGraph := Context.head [] _
  have he : Context [newGraph] (either (equal 11 11) (member 6 11)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 11))
  exact .mp he (Context.conjunctionRight (.mp hg (.closed hi')))

/-- An actual supplied pair object and its graph membership introduce its
edge under graphFormula's own existential binder. -/
def new_pair_edge_intro : KDerivation
    (imp (both (member 9 11) newPair) (graphFormula 9 0 1).encode) := by
  let f : Formula := ((Formula.member 9 19).imp (pairFormula 19 0 1).not).not
  have hi := exists_variable_intro 19 11 f (by decide) (by decide) (by decide)
  have hf : (replace 19 11 f).encode = both (member 9 11) newPair := by
    have hr : replace 19 11 f = ((Formula.member 9 11).imp (pairFormula 11 0 1).not).not := by decide
    rw [hr]
    rfl
  have hg : existsCode 19 f.encode = (graphFormula 9 0 1).encode := rfl
  rw [hf,hg] at hi
  exact hi

/-- The new pair provides the graph edge from source endpoint 0 to target 28
when 28 is explicitly equal to target endpoint 1. -/
def new_top_edge : KDerivation (imp newGraph (imp newPair
    (imp (equal 28 1) (graphFormula 9 0 28).encode))) := by
  have hrepl : replace 1 28 (graphFormula 9 0 1) = graphFormula 9 0 28 := by decide
  have ht := (CompactNamed.equalityReplace 1 28 (graphFormula 9 0 1)
    (by decide) (by decide)).1
  rw [hrepl] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 28 1,newPair,newGraph]
  have he : Context Γ (equal 28 1) := Context.head _ _
  have hp : Context Γ newPair := .hypothesis (by simp [Γ])
  have hg : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 9 11) := .mp hg (.closed adjoin_contains_new_pair)
  have h01 : Context Γ (graphFormula 9 0 1).encode :=
    .mp (Context.conjunctionIntro hm hp) (.closed new_pair_edge_intro)
  exact .mp h01 (.mp (Context.eqSymm he) (.closed ht))

/-- Top-target case of the exact renamed right bijection witness body. The
edge-split and old-edge target bound remain explicit K proof-data inputs. -/
def top_case
    (hSplit : KDerivation (imp newGraph (imp newPair (imp newEdge (either oldEdge addedCoordinates)))))
    (hClean : KDerivation (imp cleanGraph (imp oldEdge (member 1 28)))) :
    KDerivation (imp sourceSuccessor (imp newGraph (imp newPair (imp cleanGraph
      (imp targetIrreflexive (imp (equal 28 1) (existsCode 2 witnessBody.encode))))))) := by
  let S := sourceSuccessor
  let A := newGraph
  let B := newPair
  let C := cleanGraph
  let D := targetIrreflexive
  let T := equal 28 1
  let Γ := [T,D,C,B,A,S]
  have hrepl : replace 2 0 witnessBody = namedBoth (.member 7 0)
      (namedBoth (graphFormula 9 0 28) (.all 4 (.imp
        (namedBoth (.member 7 4) (graphFormula 9 4 28)) (.equal 4 0)))) := by decide
  have hintro := exists_variable_intro 2 0 witnessBody (by decide) (by decide) (by decide)
  rw [hrepl] at hintro
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ht : Context Γ T := Context.head _ _
  have hm : Context Γ (member 7 0) := .mp hs (.closed
    (successor_contains_input 0 7 14 (by decide) (by decide)))
  have hg : Context Γ (graphFormula 9 0 28).encode :=
    .mp ht (.mp hb (.mp ha (.closed new_top_edge)))
  have hu : Context Γ (allCode 4 (imp (both (member 7 4) newEdge) (equal 4 0))) :=
    .mp ht (.mp hd (.mp hc (.mp hb (.mp ha (.closed (top_unique hSplit hClean))))))
  have hbody := Context.conjunctionIntro hm (Context.conjunctionIntro hg hu)
  exact .mp hbody (.closed hintro)

theorem top_case_certificate
    (hSplit : KDerivation (imp newGraph (imp newPair (imp newEdge (either oldEdge addedCoordinates)))))
    (hClean : KDerivation (imp cleanGraph (imp oldEdge (member 1 28)))) :
    theoremCode (certificate (top_case hSplit hClean)) =
      imp sourceSuccessor (imp newGraph (imp newPair (imp cleanGraph
        (imp targetIrreflexive (imp (equal 28 1) (existsCode 2 witnessBody.encode)))))) :=
  certificate_correct (top_case hSplit hClean)

end PASoundness.PAtoCompactSuccRightTopCase

#print axioms PASoundness.PAtoCompactSuccRightTopCase.top_case
#print axioms PASoundness.PAtoCompactSuccRightTopCase.top_case_certificate
