import PASoundness.PAtoCompactKuratowskiInjectivity
import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactGraphContextElim
import PASoundness.CompactFreshen

/-! Literal K no-spurious-edge split for a supplied composition graph
adjunction. The old graph, newly adjoined pair and new graph remain explicit
hypotheses; no graph existence or composition invariant is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionNoSpurious
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactGraphWitnessRules
open PASoundness.PAtoCompactGraphContextElim PASoundness.PAtoCompactKuratowskiInjectivity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def conclusion : Formula := namedEither (graphFormula 9 2 3)
  (namedBoth (.equal 2 10) (.equal 3 12))

def adjacent : Nat := adjoinCode 9 16 17 18

def selected : Nat := (pairFormula 16 10 12).encode

private theorem names_lt : ∀ v ∈ conclusion.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ conclusion.names.sup id at hm
  have hb : conclusion.names.sup id < 30 := by decide
  omega

private def freshConclusion := freshen conclusion 30 names_lt

private def conclusion_vacuity : KDerivation
    (imp conclusion.encode (allCode 19 conclusion.encode)) :=
  compose freshConclusion.equivalent.forward
    (compose (freshConclusion.formula.vacuity 19 (by decide))
      (allCongr 19 freshConclusion.equivalent.backward))

/-- Inspect an entry of the explicitly supplied point-adjunction graph. -/
def adjoin_inspect : KDerivation
    (imp adjacent (imp (member 17 19) (either (member 9 19) (equal 19 16)))) := by
  let E := either (equal 19 16) (member 9 19)
  let B := both (imp (member 17 19) E) (imp E (member 17 19))
  let f : Formula := namedBoth (.imp (.member 17 18)
      (namedEither (.equal 18 16) (.member 9 18)))
    (.imp (namedEither (.equal 18 16) (.member 9 18)) (.member 17 18))
  have hi := universalInstance 18 19 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp adjacent B) := by
    simpa [f, adjacent, adjoinCode, B, E, namedBoth, namedEither, Formula.encode,
      CompactNamed.replace, CompactNamed.rename, CompactProof.both,
      CompactProof.neg, CompactDerivations.either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 17 19,adjacent]
  have ha : Context Γ adjacent := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 17 19) := Context.head _ _
  have hb : Context Γ B := .mp ha (.closed hi')
  have he : Context Γ E := .mp hm (Context.conjunctionLeft hb)
  apply Context.disjunctionElim he
  · exact Context.disjunctionRight (a := member 9 19) (Context.head _ _)
  · exact Context.disjunctionLeft (b := equal 19 16) (Context.head _ _)

/-- Pair-coordinate agreement when the alleged entry is the adjoined entry.
The pair representative may be nonunique; only its coordinates are compared. -/
def pair_alias : KDerivation (imp (equal 19 16)
    (imp (pairFormula 19 2 3).encode (imp selected
      (both (equal 2 10) (equal 3 12))))) := by
  have hrepl : replace 19 16 (pairFormula 19 2 3) = pairFormula 16 2 3 := by decide
  have ht := (equalityReplace 19 16 (pairFormula 19 2 3)
    (by decide) (by decide)).1
  rw [hrepl] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [selected,(pairFormula 19 2 3).encode,equal 19 16]
  have he : Context Γ (equal 19 16) := .hypothesis (by simp [Γ])
  have ha : Context Γ (pairFormula 19 2 3).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ selected := Context.head _ _
  have ha' : Context Γ (pairFormula 16 2 3).encode := .mp ha (.mp he (.closed ht))
  have hs : Context Γ (both (equal 10 2) (equal 12 3)) :=
    .mp ha' (.mp hb (.closed (pair_coordinates 16 10 12 2 3 (by decide))))
  exact Context.conjunctionIntro (Context.eqSymm (Context.conjunctionLeft hs))
    (Context.eqSymm (Context.conjunctionRight hs))

/-- An edge of the new graph either was an old edge or has the supplied
appended pair's two coordinates. -/
def no_spurious_edge : KDerivation
    (imp adjacent (imp selected (imp (graphFormula 17 2 3).encode conclusion.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let P := (pairFormula 19 2 3).encode
  let B := both (member 17 19) P
  let Γ := [selected,adjacent]
  have ha : Context Γ adjacent := .hypothesis (by simp [Γ])
  have hq : Context Γ selected := Context.head _ _
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 19 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = selected
    · subst h
      exact (pairFormula 16 10 12).vacuity 19 (by decide)
    · have he' : h = adjacent := hh.resolve_left he
      subst h
      let f := namedAdjoin 9 16 17 18
      have hv := f.vacuity 19 (by decide)
      simpa [f, namedAdjoin, adjacent, namedBoth, namedEither, Formula.encode, adjoinCode,
        CompactProof.both, CompactProof.neg, CompactDerivations.either] using hv
  have hs : Context Γ (imp B conclusion.encode) := by
    apply Context.deduction
    have hb : Context (B :: Γ) B := Context.head _ _
    have hm : Context (B :: Γ) (member 17 19) := Context.conjunctionLeft hb
    have hp : Context (B :: Γ) P := Context.conjunctionRight hb
    have ha' : Context (B :: Γ) adjacent := Context.under ha _
    have hq' : Context (B :: Γ) selected := Context.under hq _
    have hc : Context (B :: Γ) (either (member 9 19) (equal 19 16)) :=
      .mp hm (.mp ha' (.closed adjoin_inspect))
    change Context (B :: Γ) (either (graphFormula 9 2 3).encode
      (both (equal 2 10) (equal 3 12)))
    apply Context.disjunctionElim hc
    · have ho : Context (member 9 19 :: B :: Γ) (member 9 19) := Context.head _ _
      have hp' : Context (member 9 19 :: B :: Γ) P := Context.under hp _
      have hg : Context (member 9 19 :: B :: Γ) (graphFormula 9 2 3).encode :=
        .mp (Context.conjunctionIntro ho hp') (.closed (graph_intro 9 2 3))
      exact Context.disjunctionLeft (b := both (equal 2 10) (equal 3 12)) hg
    · have he : Context (equal 19 16 :: B :: Γ) (equal 19 16) := Context.head _ _
      have hp' : Context (equal 19 16 :: B :: Γ) P := Context.under hp _
      have hq'' : Context (equal 19 16 :: B :: Γ) selected := Context.under hq' _
      have hr : Context (equal 19 16 :: B :: Γ) (both (equal 2 10) (equal 3 12)) :=
        .mp hq'' (.mp hp' (.mp he (.closed pair_alias)))
      exact Context.disjunctionRight (a := (graphFormula 9 2 3).encode) hr
  exact graph_context_imp Γ 17 2 3 conclusion hv conclusion_vacuity hs

theorem no_spurious_edge_certificate : theoremCode (certificate no_spurious_edge) =
    imp adjacent (imp selected (imp (graphFormula 17 2 3).encode conclusion.encode)) :=
  certificate_correct no_spurious_edge

end PASoundness.PAtoCompactCompositionNoSpurious

#print axioms PASoundness.PAtoCompactCompositionNoSpurious.no_spurious_edge
#print axioms PASoundness.PAtoCompactCompositionNoSpurious.no_spurious_edge_certificate
