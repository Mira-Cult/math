import PASoundness.PAtoCompactGraphMeaning

/-! A proposed first-order relation for multiplication on the candidate
ordinal domain. It asks for a represented graph from ordered pairs of input
members to output members, preserving the lexicographic order. This file
does not prove that K can collect such a graph, nor quotient congruence,
operation totality, PA axioms, or an interpretation. The named syntax's
bottom is interpreted here only in standard HF semantics; its compact code is
literal `member 0 0` and requires separate care in arbitrary K models. -/
namespace PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphMeaning PASoundness.PAtoCompactPairMeaning
open PASoundness.PAtoCompactOrderedPair PASoundness.HFCoding
open PASoundness.CompactMatrix (Environment bit update)

private def both (a b : Formula) : Formula := (a.imp b.not).not
private def either (a b : Formula) : Formula := a.not.imp b
private def iffF (a b : Formula) : Formula := both (a.imp b) (b.imp a)

/-- The proposed graph has name 6; its edge for the pair (a,b) and
value c is witnessed by name 18. To read the parameters literally their
names must avoid 18–22; the fixed calls below satisfy this. -/
def tripleFormula (a b c : Nat) : Formula :=
  .ex 18 (both (pairFormula 18 a b) (graphFormula 6 18 c))

/-- The represented graph denotes an order-preserving bijection from the
lexicographic product of members of names 0 and 1 onto the members of name 2.
Quantifier names are local. The use of an existential graph is an explicit
condition, not a claim that K can collect the product or graph. -/
def forwardFormula : Formula :=
  (.all 3 (.imp (.member 0 3) (.all 4 (.imp (.member 1 4) (.ex 5
    (both (.member 2 5) (both (tripleFormula 3 4 5)
      (.all 9 (.imp (both (.member 2 9) (tripleFormula 3 4 9)) (.equal 9 5))))))))))

def reverseFormula : Formula :=
  .all 5 (.imp (.member 2 5) (.ex 3 (.ex 4
    (both (.member 0 3) (both (.member 1 4) (both (tripleFormula 3 4 5)
      (.all 7 (.all 8 (.imp (both (.member 0 7) (both (.member 1 8)
        (tripleFormula 7 8 5))) (both (.equal 7 3) (.equal 8 4)))))))))))

def lexFormula : Formula :=
  .all 3 (.all 4 (.all 5 (.all 7 (.all 8 (.all 9
    (.imp (both (.member 0 3) (both (.member 1 4) (both (.member 2 5)
      (both (.member 0 7) (both (.member 1 8) (both (.member 2 9)
        (both (tripleFormula 3 4 5) (tripleFormula 7 8 9))))))))
      (iffF (.member 9 5) (either (.member 7 3)
        (both (.equal 3 7) (.member 8 4))))))))))

def productMatrix : Formula := both forwardFormula (both reverseFormula lexFormula)

def productFormula : Formula := .ex 6 productMatrix

/-- Free-name calculation is syntactic named IR only. -/
theorem product_free : productFormula.free = {0,1,2} := by decide

/-- A triple edge is represented by a canonical ordered-pair code in the
standard HF model. This semantic fact is not a K graph-existence theorem. -/
theorem triple_realize_iff (a b c : Nat) (ρ : Environment)
    (ha : a ≠ 18 ∧ a ≠ 19 ∧ a ≠ 20 ∧ a ≠ 21 ∧ a ≠ 22)
    (hb : b ≠ 18 ∧ b ≠ 19 ∧ b ≠ 20 ∧ b ≠ 21 ∧ b ≠ 22)
    (hc : c ≠ 18 ∧ c ≠ 19 ∧ c ≠ 20 ∧ c ≠ 21 ∧ c ≠ 22) :
    (tripleFormula a b c).Realize ρ ↔
      graphRel (ρ 6) (orderedPair ⟨ρ a⟩ ⟨ρ b⟩).code (ρ c) := by
  unfold tripleFormula
  simp [both, Formula.Realize, Formula.not,
    pairFormula_realize_iff 18 a b _ (by decide) ⟨ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2⟩
      ⟨hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2⟩,
    graphFormula_realize_iff 6 18 c _ (by decide) (by decide)
      ⟨hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2⟩,
    update, ha.1, hb.1, hc.1]

/-- Standard-HF graph relation for a pair of input objects and one output. -/
def tripleRel (g a b c : Nat) : Prop :=
  graphRel g (orderedPair ⟨a⟩ ⟨b⟩).code c

/-- The forward part expresses a unique output for each input pair. -/
theorem forward_meaning (ρ : Environment) :
    forwardFormula.Realize ρ ↔
      ∀ a, bit (ρ 0) a = true → ∀ b, bit (ρ 1) b = true →
        ∃ c, bit (ρ 2) c = true ∧ tripleRel (ρ 6) a b c ∧
          ∀ c', bit (ρ 2) c' = true → tripleRel (ρ 6) a b c' → c' = c := by
  simp [forwardFormula, both, Formula.Realize, Formula.not,
    triple_realize_iff 3 4 5 _ (by decide) (by decide) (by decide),
    triple_realize_iff 3 4 9 _ (by decide) (by decide) (by decide),
    update, tripleRel]

/-- The reverse part expresses a unique input pair for each output. -/
theorem reverse_meaning (ρ : Environment) :
    reverseFormula.Realize ρ ↔
      ∀ c, bit (ρ 2) c = true → ∃ a, ∃ b,
        bit (ρ 0) a = true ∧ bit (ρ 1) b = true ∧ tripleRel (ρ 6) a b c ∧
          ∀ a', ∀ b', bit (ρ 0) a' = true → bit (ρ 1) b' = true →
            tripleRel (ρ 6) a' b' c → a' = a ∧ b' = b := by
  simp [reverseFormula, both, Formula.Realize, Formula.not,
    triple_realize_iff 3 4 5 _ (by decide) (by decide) (by decide),
    triple_realize_iff 7 8 5 _ (by decide) (by decide) (by decide),
    update, tripleRel]
  constructor
  · intro h c hc
    obtain ⟨a, ha, b, hb, hab, hu⟩ := h c hc
    refine ⟨a, ha, b, hb, hab, ?_⟩
    intro a' b' ha' hb' hrel
    exact hu a' ha' b' hb' hrel
  · intro h c hc
    obtain ⟨a, ha, b, hb, hab, hu⟩ := h c hc
    refine ⟨a, ha, b, hb, hab, ?_⟩
    intro a' ha' b' hb' hrel
    exact hu a' b' ha' hb' hrel

/-- The order clause says output membership is exactly lexicographic input
membership, in standard HF semantics. -/
theorem lex_meaning (ρ : Environment) :
    lexFormula.Realize ρ ↔
      ∀ a b c a' b' c',
        bit (ρ 0) a = true → bit (ρ 1) b = true → bit (ρ 2) c = true →
        bit (ρ 0) a' = true → bit (ρ 1) b' = true → bit (ρ 2) c' = true →
        tripleRel (ρ 6) a b c → tripleRel (ρ 6) a' b' c' →
        (bit c' c = true ↔ bit a' a = true ∨ (a = a' ∧ bit b' b = true)) := by
  simp [lexFormula, both, either, iffF, Formula.Realize, Formula.not,
    triple_realize_iff 3 4 5 _ (by decide) (by decide) (by decide),
    triple_realize_iff 7 8 9 _ (by decide) (by decide) (by decide),
    update, tripleRel, or_iff_not_imp_left, iff_def]

/-- The proposed relation's full standard-HF meaning, retaining the
represented graph witness. This statement does not say that a suitable graph
exists for any particular inputs. -/
def productSemantics (x y z : Nat) : Prop :=
  ∃ g,
    (∀ a, bit x a = true → ∀ b, bit y b = true →
      ∃ c, bit z c = true ∧ tripleRel g a b c ∧
        ∀ c', bit z c' = true → tripleRel g a b c' → c' = c) ∧
    (∀ c, bit z c = true → ∃ a, ∃ b,
      bit x a = true ∧ bit y b = true ∧ tripleRel g a b c ∧
        ∀ a', ∀ b', bit x a' = true → bit y b' = true →
          tripleRel g a' b' c → a' = a ∧ b' = b) ∧
    (∀ a b c a' b' c',
      bit x a = true → bit y b = true → bit z c = true →
      bit x a' = true → bit y b' = true → bit z c' = true →
      tripleRel g a b c → tripleRel g a' b' c' →
      (bit c' c = true ↔ bit a' a = true ∨ (a = a' ∧ bit b' b = true)))

private theorem both_realize (a b : Formula) (ρ : Environment) :
    (both a b).Realize ρ ↔ a.Realize ρ ∧ b.Realize ρ := by
  simp [both, Formula.Realize, Formula.not]

theorem product_realize_iff (ρ : Environment) :
    productFormula.Realize ρ ↔ productSemantics (ρ 0) (ρ 1) (ρ 2) := by
  unfold productFormula productMatrix productSemantics
  simp only [Formula.Realize, both_realize, forward_meaning, reverse_meaning, lex_meaning]
  simp [update]

end PASoundness.PAtoCompactMultiplicationCandidate

#print axioms PASoundness.PAtoCompactMultiplicationCandidate.product_free
#print axioms PASoundness.PAtoCompactMultiplicationCandidate.triple_realize_iff
#print axioms PASoundness.PAtoCompactMultiplicationCandidate.forward_meaning
#print axioms PASoundness.PAtoCompactMultiplicationCandidate.reverse_meaning
#print axioms PASoundness.PAtoCompactMultiplicationCandidate.lex_meaning
#print axioms PASoundness.PAtoCompactMultiplicationCandidate.product_realize_iff
