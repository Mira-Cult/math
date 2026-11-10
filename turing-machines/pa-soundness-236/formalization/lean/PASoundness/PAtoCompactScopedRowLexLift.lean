import PASoundness.CompactNamed

/-! Generic K proof-data composition for retaining witnesses under nested
existentials. Every needed vacuity and point implication is an explicit input.
This module does not establish any matrix clause, graph construction,
multiplication totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactScopedRowLexLift
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Distribute an explicitly guarded pointwise proof through one retained
conjunct. This proof changes neither the antecedent nor its witness. -/
def retain_conjunct (e a b c : Nat)
    (h : KDerivation (imp (both e a) (imp b c))) :
    KDerivation (imp e (imp (both a b) (both a c))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [both a b,e]
  have hab : Context Γ (both a b) := .head _ _
  have he : Context Γ e := .hypothesis (by simp [Γ])
  have ha : Context Γ a := Context.conjunctionLeft hab
  have hb : Context Γ b := Context.conjunctionRight hab
  have hc : Context Γ c := .mp hb (.mp (Context.conjunctionIntro he ha) (.closed h))
  exact Context.conjunctionIntro ha hc

/-- Four nested existential witnesses at 40, 10, 6 and 64, each retaining the
preceding conjunct. Variables are literal compact labels; no distinctness of
the denoted objects is assumed. -/
def nested (a b c r : Nat) : Nat :=
  existsCode 40 (both a (existsCode 10 (both b (existsCode 6 (both c (existsCode 64 r))))))

/-- Lift a scoped pointwise K proof through the four existential witnesses.
Vacuity for each accumulated context is supplied explicitly, so no claim is
made that arbitrary formulas avoid the witness labels. -/
def lift_scoped (e a b c r s : Nat)
    (v40 : KDerivation (imp e (allCode 40 e)))
    (v10 : KDerivation (imp (both e a) (allCode 10 (both e a))))
    (v6 : KDerivation (imp (both (both e a) b) (allCode 6 (both (both e a) b))))
    (v64 : KDerivation (imp (both (both (both e a) b) c)
      (allCode 64 (both (both (both e a) b) c))))
    (point : KDerivation (imp (both (both (both e a) b) c) (imp r s))) :
    KDerivation (imp e (imp (nested a b c r) (nested a b c s))) := by
  have h64 := conditionalExistsCongr 64 v64 point
  have h6point := retain_conjunct (both (both e a) b) c _ _ h64
  have h6 := conditionalExistsCongr 6 v6 h6point
  have h10point := retain_conjunct (both e a) b _ _ h6
  have h10 := conditionalExistsCongr 10 v10 h10point
  have h40point := retain_conjunct e a _ _ h10
  have h40 := conditionalExistsCongr 40 v40 h40point
  simpa [nested] using h40

theorem lift_scoped_certificate (e a b c r s : Nat)
    (v40 : KDerivation (imp e (allCode 40 e)))
    (v10 : KDerivation (imp (both e a) (allCode 10 (both e a))))
    (v6 : KDerivation (imp (both (both e a) b) (allCode 6 (both (both e a) b))))
    (v64 : KDerivation (imp (both (both (both e a) b) c)
      (allCode 64 (both (both (both e a) b) c))))
    (point : KDerivation (imp (both (both (both e a) b) c) (imp r s))) :
    theoremCode (certificate (lift_scoped e a b c r s v40 v10 v6 v64 point)) =
      imp e (imp (nested a b c r) (nested a b c s)) := certificate_correct _
end PASoundness.PAtoCompactScopedRowLexLift
#print axioms PASoundness.PAtoCompactScopedRowLexLift.retain_conjunct
#print axioms PASoundness.PAtoCompactScopedRowLexLift.lift_scoped
#print axioms PASoundness.PAtoCompactScopedRowLexLift.lift_scoped_certificate
