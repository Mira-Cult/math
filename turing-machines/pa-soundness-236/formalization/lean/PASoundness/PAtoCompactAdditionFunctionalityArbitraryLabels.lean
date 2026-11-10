import PASoundness.PAtoCompactAdditionFunctionalityInstantiate

/-! Instantiate the same-input addition functionality frame at arbitrary
free labels, including aliased labels, using four fresh temporary names. -/
namespace PASoundness.PAtoCompactAdditionFunctionalityArbitraryLabels

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdditionFunctionalityInstantiate
open PASoundness.PAtoCompactAdditionDomainFunctionality

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def temporary (x y z w : Nat) : Nat := max (max x y) (max z w) + 40
def highBase (x y z w : Nat) : Nat := temporary x y z w + 100

/-- All four input/output labels may alias. The proof stages them through
distinct temporary names before substituting the requested labels. -/
def functionality_at_high_base (x y z w : Nat) :
    KDerivation (frame (highBase x y z w) x y z w).encode := by
  let t := temporary x y z w
  let b := highBase x y z w
  have ht : 28 < t := by dsimp [t,temporary]; omega
  have hx : x < t := by dsimp [t,temporary]; omega
  have hy : y < t := by dsimp [t,temporary]; omega
  have hz : z < t := by dsimp [t,temporary]; omega
  have hw : w < t := by dsimp [t,temporary]; omega
  have htb : t + 3 < b := by dsimp [b,highBase,t]; omega
  have h0 : KDerivation (frame b 28 1 0 8).encode := by
    simpa only [frame, PASoundness.PAtoCompactAdditionDomainFunctionality.guard, Formula.encode] using
      addition_domain_functionality_allocated b b b b b b b (by omega) (by omega) (by omega)
  have h1 : KDerivation (frame b t 1 0 8).encode := by
    simpa [rename] using instantiate_name b 28 1 0 8 28 t (by omega) (by omega) h0
  have h2 : KDerivation (frame b t (t+1) 0 8).encode := by
    simpa [rename, show t ≠ 1 by omega] using instantiate_name b t 1 0 8 1 (t+1) (by omega) (by omega) h1
  have h3 : KDerivation (frame b t (t+1) (t+2) 8).encode := by
    simpa [rename, show t ≠ 0 by omega, show t+1 ≠ 0 by omega] using
      instantiate_name b t (t+1) 0 8 0 (t+2) (by omega) (by omega) h2
  have h4 : KDerivation (frame b t (t+1) (t+2) (t+3)).encode := by
    simpa [rename, show t ≠ 8 by omega, show t+1 ≠ 8 by omega, show t+2 ≠ 8 by omega] using
      instantiate_name b t (t+1) (t+2) 8 8 (t+3) (by omega) (by omega) h3
  have h5 : KDerivation (frame b x (t+1) (t+2) (t+3)).encode := by
    simpa [rename, show t+1 ≠ t by omega, show t+2 ≠ t by omega, show t+3 ≠ t by omega] using
      instantiate_name b t (t+1) (t+2) (t+3) t x (by omega) (by omega) h4
  have h6 : KDerivation (frame b x y (t+2) (t+3)).encode := by
    simpa [rename, show x ≠ t+1 by omega, show t+2 ≠ t+1 by omega, show t+3 ≠ t+1 by omega] using
      instantiate_name b x (t+1) (t+2) (t+3) (t+1) y (by omega) (by omega) h5
  have h7 : KDerivation (frame b x y z (t+3)).encode := by
    simpa [rename, show x ≠ t+2 by omega, show y ≠ t+2 by omega, show t+3 ≠ t+2 by omega] using
      instantiate_name b x y (t+2) (t+3) (t+2) z (by omega) (by omega) h6
  have h8 : KDerivation (frame b x y z w).encode := by
    simpa [rename, show x ≠ t+3 by omega, show y ≠ t+3 by omega, show z ≠ t+3 by omega] using
      instantiate_name b x y z (t+3) (t+3) w (by omega) (by omega) h7
  exact h8

theorem functionality_at_high_base_certificate (x y z w : Nat) :
    theoremCode (certificate (functionality_at_high_base x y z w)) =
      (frame (highBase x y z w) x y z w).encode := certificate_correct _

end PASoundness.PAtoCompactAdditionFunctionalityArbitraryLabels

#print axioms PASoundness.PAtoCompactAdditionFunctionalityArbitraryLabels.temporary
#print axioms PASoundness.PAtoCompactAdditionFunctionalityArbitraryLabels.highBase
#print axioms PASoundness.PAtoCompactAdditionFunctionalityArbitraryLabels.functionality_at_high_base
#print axioms PASoundness.PAtoCompactAdditionFunctionalityArbitraryLabels.functionality_at_high_base_certificate
