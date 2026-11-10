import PASoundness.PAtoCompactSuccCongruenceMatrix
import PASoundness.PAtoCompactSuccCongruenceWitnessVacuity
import PASoundness.PAtoCompactSuccCongruenceWitnessExists
import PASoundness.PAtoCompactKuratowskiInjectivity

/-! Eliminate the supplied new pair and point-adjoined graph witnesses from
the checked successor-isomorphism matrix derivation. The old isomorphism,
clean graph, both successor graphs and both transitivity formulas remain
explicit antecedents. This does not yet derive clean-graph existence or the
unconditional quotient congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceWitnessElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccCongruenceMixedOrder
open PASoundness.PAtoCompactSuccCongruenceMatrix PASoundness.PAtoCompactSuccCongruenceWitnessVacuity
open PASoundness.PAtoCompactSuccCongruenceWitnessExists PASoundness.PAtoCompactKuratowskiInjectivity

/-- Eliminate a closed supplied existential witness from the second
antecedent, with explicit vacuity for the retained antecedent and target. -/
def discharge_witness (x A B C : Nat)
    (hvA : KDerivation (imp A (allCode x A)))
    (hvC : KDerivation (imp C (allCode x C)))
    (h : KDerivation (imp A (imp B C)))
    (hex : KDerivation (existsCode x B)) : KDerivation (imp A C) := by
  have hlift := lift_exists_second x A B C hvA hvC h
  apply Context.closeEmpty
  apply Context.deduction
  exact .mp (.closed hex) (.mp (Context.head [] A) (.closed hlift))

/-- A concrete matrix entails an existential matrix with a fresh graph name. -/
def output_intro : KDerivation (imp newMatrix freshOutput.encode) := by
  have hi := CompactNamed.existsIntroduce 9 newMatrixNamed (by decide)
  have hi' : KDerivation (imp newMatrix (existsCode 9 newMatrix)) := by
    simpa only [newMatrix_encode, Formula.encode] using hi
  exact compose hi' output_alpha_forward

/-- The retained core, given the two concrete witnesses, yields the fresh
existential target matrix. -/
def local_matrix : KDerivation (imp (both retainedCode newPair)
    (imp newGraph freshOutput.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [newGraph,both retainedCode newPair]
  have ha : Context Γ newGraph := Context.head _ _
  have hrp : Context Γ (both retainedCode newPair) := .hypothesis (by simp [Γ])
  have hr : Context Γ retainedCode := Context.conjunctionLeft hrp
  have hp : Context Γ newPair := Context.conjunctionRight hrp
  have hm : Context Γ oldMatrix := Context.conjunctionLeft hr
  have h1 := Context.conjunctionRight hr
  have hg : Context Γ cleanGraph := Context.conjunctionLeft h1
  have h2 := Context.conjunctionRight h1
  have hs : Context Γ sourceSuccessor := Context.conjunctionLeft h2
  have h3 := Context.conjunctionRight h2
  have ht : Context Γ targetSuccessor := Context.conjunctionLeft h3
  have h4 := Context.conjunctionRight h3
  have hts : Context Γ sourceTrans := Context.conjunctionLeft h4
  have htt : Context Γ targetTrans := Context.conjunctionRight h4
  have hc : Context Γ corePremises := Context.conjunctionIntro hm (Context.conjunctionIntro hg
    (Context.conjunctionIntro hs (Context.conjunctionIntro ht (Context.conjunctionIntro hp ha))))
  have hmatrix : Context Γ newMatrix := .mp htt (.mp hts (.mp hc (.closed successor_matrix)))
  exact .mp hmatrix (.closed output_intro)

/-- With a retained clean graph and its supplied old matrix and successors,
K constructs some graph satisfying the exact successor-isomorphism matrix. -/
def successor_graph_exists : KDerivation
    (imp retainedCode (existsCode 9 newMatrix)) := by
  let A : Formula := namedBoth retainedNamed (pairFormula 11 0 1)
  have hA : A.encode = both retainedCode newPair := by rfl
  have hvA : KDerivation (imp (both retainedCode newPair)
      (allCode 9 (both retainedCode newPair))) := by
    have h := A.vacuity 9 (by decide)
    simpa only [hA] using h
  have hgraph : KDerivation (imp (both retainedCode newPair) freshOutput.encode) :=
    discharge_witness 9 (both retainedCode newPair) newGraph freshOutput.encode
      hvA output_vacuity_9 local_matrix adjoin_exists
  have hcurried : KDerivation (imp retainedCode (imp newPair freshOutput.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [newPair,retainedCode]
    have hp : Context Γ newPair := Context.head _ _
    have hr : Context Γ retainedCode := .hypothesis (by simp [Γ])
    exact .mp (Context.conjunctionIntro hr hp) (.closed hgraph)
  have hout : KDerivation (imp retainedCode freshOutput.encode) :=
    discharge_witness 11 retainedCode newPair freshOutput.encode
      retained_vacuity_11 output_vacuity_11 hcurried pair_exists
  exact compose hout output_alpha_backward

theorem successor_graph_exists_certificate : theoremCode (certificate successor_graph_exists) =
    imp retainedCode (existsCode 9 newMatrix) := certificate_correct successor_graph_exists

end PASoundness.PAtoCompactSuccCongruenceWitnessElim

#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessElim.successor_graph_exists
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessElim.successor_graph_exists_certificate
