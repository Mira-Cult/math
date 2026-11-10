import PASoundness.CompactDerivations

/-! Swapping two existential quantifiers as finite K proof data. No freshness
condition is needed: the quantifiers themselves bind the same literal names
on both sides, even when those names coincide. -/
namespace PASoundness.PAtoCompactExistsCommute

open PASoundness.CompactProof PASoundness.CompactDerivations

/-- Exchange two nested existential quantifiers by contrapositive, universal
commutation and classical double-negation elimination/introduction. -/
def exists_commute (x y a : Nat) : KDerivation
    (imp (existsCode x (existsCode y a)) (existsCode y (existsCode x a))) := by
  have h1 := allCongr y (doubleNegElim (allCode x (neg a)))
  have h2 := allCommute y x (neg a)
  have h3 := allCongr x (doubleNegIntro (allCode y (neg a)))
  have h := contrapose (compose h1 (compose h2 h3))
  exact h

theorem exists_commute_certificate (x y a : Nat) :
    theoremCode (certificate (exists_commute x y a)) =
      imp (existsCode x (existsCode y a)) (existsCode y (existsCode x a)) :=
  certificate_correct _

#print axioms exists_commute
#print axioms exists_commute_certificate
end PASoundness.PAtoCompactExistsCommute
