import PASoundness.PAtoCompactKuratowskiSyntax
import PASoundness.CompactQuantifiers

/-! Capture-safe introduction of the displayed quotient proposal's pair
output variable. This is a K proof interface, not a pair-existence theorem or
an interpretation of arithmetic. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactKuratowskiFresh
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiSyntax

/-- The explicitly displayed pair formula binds exactly these three names,
independently of its displayed input names. -/
theorem pair_binders (p a b : Nat) :
    (pairFormula p a b).binders = {20,21,22} := by
  rw [pair_formula_named]
  simp [PAtoCompactSingleton.namedSingleton, PAtoCompactUnorderedPair.namedPair,
    PAtoCompactZeroSuccessor.namedBoth, PAtoCompactZeroSuccessor.namedEither,
    CompactNamed.Formula.binders]

/-- Name 19 can be quantified outside the concrete pair formula. -/
theorem pair_output_not_bound (a b : Nat) : 19 ∉ (pairFormula 19 a b).binders := by
  rw [pair_binders]
  decide

/-- Same-name output introduction for the literal K formula. This does not
supply a proof of the premise. -/
def pair_output_intro (a b : Nat) :
    KDerivation (imp (pairFormula 19 a b).encode
      (existsCode 19 (pairFormula 19 a b).encode)) :=
  CompactNamed.existsIntroduce 19 (pairFormula 19 a b) (pair_output_not_bound a b)

/-- The selected helper labels are absent from the concrete graph formula
for endpoint names 2 and 3. This is named-syntax freshness. -/
theorem helper_names_fresh (k : Nat) (hk : k = 23 ∨ k = 24) :
    k ∉ (pairFormula 19 2 3).names := by
  rcases hk with rfl | rfl <;> decide

/-- The concrete pair graph can be generalized over either helper name. -/
def pair_helper_vacuity (k : Nat) (hk : k = 23 ∨ k = 24) :
    KDerivation (imp (pairFormula 19 2 3).encode
      (allCode k (pairFormula 19 2 3).encode)) :=
  (pairFormula 19 2 3).vacuity k (helper_names_fresh k hk)

/-- The existential output formula also has fresh helper names. -/
def pair_exists_helper_vacuity (k : Nat) (hk : k = 23 ∨ k = 24) :
    KDerivation (imp (existsCode 19 (pairFormula 19 2 3).encode)
      (allCode k (existsCode 19 (pairFormula 19 2 3).encode))) := by
  let f : CompactNamed.Formula := .ex 19 (pairFormula 19 2 3)
  have h : k ∉ f.names := by
    rcases hk with rfl | rfl <;> decide
  exact f.vacuity k h

theorem pair_output_intro_certificate (a b : Nat) :
    theoremCode (certificate (pair_output_intro a b)) =
      imp (pairFormula 19 a b).encode (existsCode 19 (pairFormula 19 a b).encode) :=
  certificate_correct (pair_output_intro a b)

end PASoundness.PAtoCompactKuratowskiFresh

#print axioms PASoundness.PAtoCompactKuratowskiFresh.pair_binders
#print axioms PASoundness.PAtoCompactKuratowskiFresh.pair_output_intro
#print axioms PASoundness.PAtoCompactKuratowskiFresh.pair_output_intro_certificate
#print axioms PASoundness.PAtoCompactKuratowskiFresh.pair_helper_vacuity
#print axioms PASoundness.PAtoCompactKuratowskiFresh.pair_exists_helper_vacuity
