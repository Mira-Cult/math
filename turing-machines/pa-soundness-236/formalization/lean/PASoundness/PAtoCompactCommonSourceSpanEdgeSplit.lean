import PASoundness.PAtoCompactCommonSourceSpanAppend
import PASoundness.PAtoCompactKuratowskiInjectivity
import PASoundness.PAtoCompactGraphContextElim
import PASoundness.CompactFreshen

/-! Edge inspection for one common-source span graph extension. For the
actual pair and graph adjunction, every new graph edge is either an old edge
or has exactly the newly selected image coordinates. This is a K proof-data
step; it does not prove the span invariant or candidate induction. -/
namespace PASoundness.PAtoCompactCommonSourceSpanEdgeSplit

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactKuratowskiInjectivity PASoundness.PAtoCompactGraphContextElim

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def edgeConclusion : Formula := namedEither (graphFormula 9 2 3)
  (namedBoth (.equal 2 11) (.equal 3 12))

theorem edgeConclusion_code : edgeConclusion.encode =
    either (graphFormula 9 2 3).encode (both (equal 2 11) (equal 3 12)) := rfl

/-- The pair found as a new graph element has the selected coordinates if it
is equal to the pair that was adjoined. The interpreted coordinates may alias. -/
def selected_pair_alias : KDerivation (imp (equal 19 16)
    (imp (pairFormula 19 2 3).encode (imp (pairFormula 16 11 12).encode
      (both (equal 2 11) (equal 3 12))))) := by
  have hrepl : replace 19 16 (pairFormula 19 2 3) = pairFormula 16 2 3 := by decide
  have ht := (equalityReplace 19 16 (pairFormula 19 2 3) (by decide) (by decide)).1
  rw [hrepl] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 16 11 12).encode, (pairFormula 19 2 3).encode, equal 19 16]
  have he : Context Γ (equal 19 16) := .hypothesis (by simp [Γ])
  have ha : Context Γ (pairFormula 19 2 3).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (pairFormula 16 11 12).encode := .head _ _
  have ha' : Context Γ (pairFormula 16 2 3).encode := .mp ha (.mp he (.closed ht))
  exact .mp hb (.mp ha' (.closed (pair_coordinates 16 2 3 11 12 (by decide))))

private theorem edgeConclusion_names_lt : ∀ v ∈ edgeConclusion.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ edgeConclusion.names.sup id at hm
  have hb : edgeConclusion.names.sup id < 30 := by decide
  omega

private def freshConclusion := freshen edgeConclusion 30 edgeConclusion_names_lt

private def edgeConclusion_vacuity : KDerivation
    (imp edgeConclusion.encode (allCode 19 edgeConclusion.encode)) :=
  compose freshConclusion.equivalent.forward
    (compose (freshConclusion.formula.vacuity 19 (by decide))
      (allCongr 19 freshConclusion.equivalent.backward))

/-- Inspect a graph element under the exact point adjunction. -/
def adjoin_element_split : KDerivation
    (imp (adjoinCode 9 16 17 18)
      (imp (member 17 19) (either (member 9 19) (equal 19 16)))) := by
  let E := either (equal 19 16) (member 9 19)
  let B := both (imp (member 17 19) E) (imp E (member 17 19))
  let f : Formula := namedBoth (.imp (.member 17 18)
      (namedEither (.equal 18 16) (.member 9 18)))
    (.imp (namedEither (.equal 18 16) (.member 9 18)) (.member 17 18))
  have hi := universalInstance 18 19 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (adjoinCode 9 16 17 18) B) := by
    simpa [f, adjoinCode, B, E, namedBoth, namedEither, Formula.encode,
      replace, rename, both, neg, either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 17 19, adjoinCode 9 16 17 18]
  have ha : Context Γ (adjoinCode 9 16 17 18) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 17 19) := .head _ _
  have hb : Context Γ B := .mp ha (.closed hi')
  have he : Context Γ E := .mp hm (Context.conjunctionLeft hb)
  apply Context.disjunctionElim he
  · exact Context.disjunctionRight (a := member 9 19) (.head _ _)
  · exact Context.disjunctionLeft (b := equal 19 16) (.head _ _)

private def oldGraphBody : Formula := match graphFormula 9 2 3 with
  | .ex _ f => f
  | _ => .truth

private def old_graph_intro : KDerivation
    (imp (both (member 9 19) (pairFormula 19 2 3).encode)
      (graphFormula 9 2 3).encode) :=
  existsIntroduce 19 oldGraphBody (by decide)

private def adjoin_vacuity : KDerivation
    (imp (adjoinCode 9 16 17 18) (allCode 19 (adjoinCode 9 16 17 18))) := by
  let f := namedAdjoin 9 16 17 18
  have hv := f.vacuity 19 (by decide)
  simpa [f, namedAdjoin, namedBoth, namedEither, Formula.encode, adjoinCode,
    both, neg, either] using hv

private def pair_vacuity : KDerivation
    (imp (pairFormula 16 11 12).encode (allCode 19 (pairFormula 16 11 12).encode)) :=
  (pairFormula 16 11 12).vacuity 19 (by decide)

/-- Every edge of the adjoined graph is old or has the selected pair's exact
coordinates. The displayed adjunction and pair remain K antecedents. -/
def adjoined_edge_split : KDerivation
    (imp (adjoinCode 9 16 17 18) (imp (pairFormula 16 11 12).encode
      (imp (graphFormula 17 2 3).encode edgeConclusion.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let P := (pairFormula 19 2 3).encode
  let B := both (member 17 19) P
  let R := both (equal 2 11) (equal 3 12)
  let G := (graphFormula 9 2 3).encode
  let A := adjoinCode 9 16 17 18
  let Q := (pairFormula 16 11 12).encode
  let Γ := [Q,A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hq : Context Γ Q := .head _ _
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 19 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = Q
    · subst h; exact pair_vacuity
    · have he' : h = A := hh.resolve_left he
      subst h; exact adjoin_vacuity
  have hs : Context Γ (imp B edgeConclusion.encode) := by
    apply Context.deduction
    have hb : Context (B :: Γ) B := .head _ _
    have hm : Context (B :: Γ) (member 17 19) := Context.conjunctionLeft hb
    have hp : Context (B :: Γ) P := Context.conjunctionRight hb
    have ha' : Context (B :: Γ) A := .under ha _
    have hq' : Context (B :: Γ) Q := .under hq _
    have hc : Context (B :: Γ) (either (member 9 19) (equal 19 16)) :=
      .mp hm (.mp ha' (.closed adjoin_element_split))
    change Context (B :: Γ) (either G R)
    apply Context.disjunctionElim hc
    · have ho : Context (member 9 19 :: B :: Γ) (member 9 19) := .head _ _
      have hp' : Context (member 9 19 :: B :: Γ) P := .under hp _
      have hg : Context (member 9 19 :: B :: Γ) G :=
        .mp (Context.conjunctionIntro ho hp') (.closed old_graph_intro)
      exact Context.disjunctionLeft (b := R) hg
    · have he : Context (equal 19 16 :: B :: Γ) (equal 19 16) := .head _ _
      have hp' : Context (equal 19 16 :: B :: Γ) P := .under hp _
      have hq'' : Context (equal 19 16 :: B :: Γ) Q := .under hq' _
      have hr : Context (equal 19 16 :: B :: Γ) R :=
        .mp hq'' (.mp hp' (.mp he (.closed selected_pair_alias)))
      exact Context.disjunctionRight (a := G) hr
  exact graph_context_imp Γ 17 2 3 edgeConclusion hv edgeConclusion_vacuity hs

theorem adjoined_edge_split_certificate :
    theoremCode (certificate adjoined_edge_split) =
      imp (adjoinCode 9 16 17 18) (imp (pairFormula 16 11 12).encode
        (imp (graphFormula 17 2 3).encode edgeConclusion.encode)) :=
  certificate_correct adjoined_edge_split

end PASoundness.PAtoCompactCommonSourceSpanEdgeSplit

#print axioms PASoundness.PAtoCompactCommonSourceSpanEdgeSplit.edgeConclusion
#print axioms PASoundness.PAtoCompactCommonSourceSpanEdgeSplit.edgeConclusion_code
#print axioms PASoundness.PAtoCompactCommonSourceSpanEdgeSplit.selected_pair_alias
#print axioms PASoundness.PAtoCompactCommonSourceSpanEdgeSplit.adjoin_element_split
#print axioms PASoundness.PAtoCompactCommonSourceSpanEdgeSplit.adjoined_edge_split
#print axioms PASoundness.PAtoCompactCommonSourceSpanEdgeSplit.adjoined_edge_split_certificate
