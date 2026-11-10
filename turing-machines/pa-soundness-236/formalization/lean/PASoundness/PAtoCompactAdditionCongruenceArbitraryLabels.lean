import PASoundness.PAtoCompactAdditionCongruenceHighBase

/-! Instantiate the fixed-label addition congruence frame at arbitrary
free names using six distinct temporary labels. -/
namespace PASoundness.PAtoCompactAdditionCongruenceArbitraryLabels

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdditionCongruenceInstantiate PASoundness.PAtoCompactAdditionCongruenceHighBase

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def temporary (x y z u v w : Nat) : Nat := max (max (max x y) (max z u)) (max v w) + 40
def highBase (x y z u v w : Nat) : Nat := temporary x y z u v w + 100

/-- All six free labels may alias; staging prevents early identification of
a source label with an input that has yet to be reassigned. -/
def congruence_at_high_base (x y z u v w : Nat) :
    KDerivation (frame (highBase x y z u v w) x y z u v w).encode := by
  let t := temporary x y z u v w
  let b := highBase x y z u v w
  have ht : 29 < t := by dsimp [t,temporary]; omega
  have hx : x < t := by dsimp [t,temporary]; omega
  have hy : y < t := by dsimp [t,temporary]; omega
  have hz : z < t := by dsimp [t,temporary]; omega
  have hu : u < t := by dsimp [t,temporary]; omega
  have hv : v < t := by dsimp [t,temporary]; omega
  have hw : w < t := by dsimp [t,temporary]; omega
  have htb : t + 5 < b := by dsimp [b,highBase,t]; omega
  have hb100 : 100 ≤ b := by dsimp [b,highBase]; omega
  have h0 : KDerivation (frame b 28 1 0 29 27 8).encode :=
    fixed_congruence_high_base b hb100
  have h1 : KDerivation (frame b t 1 0 29 27 8).encode := by
    simpa [rename, show 1 ≠ 28 by omega, show 0 ≠ 28 by omega, show 29 ≠ 28 by omega, show 27 ≠ 28 by omega, show 8 ≠ 28 by omega] using
      instantiate_name b 28 1 0 29 27 8 28 t (by omega) (by omega) h0
  have h2 : KDerivation (frame b t (t+1) 0 29 27 8).encode := by
    simpa [rename, show t ≠ 1 by omega, show 0 ≠ 1 by omega, show 29 ≠ 1 by omega, show 27 ≠ 1 by omega, show 8 ≠ 1 by omega] using
      instantiate_name b t 1 0 29 27 8 1 (t+1) (by omega) (by omega) h1
  have h3 : KDerivation (frame b t (t+1) (t+2) 29 27 8).encode := by
    simpa [rename, show t ≠ 0 by omega, show (t+1) ≠ 0 by omega, show 29 ≠ 0 by omega, show 27 ≠ 0 by omega, show 8 ≠ 0 by omega] using
      instantiate_name b t (t+1) 0 29 27 8 0 (t+2) (by omega) (by omega) h2
  have h4 : KDerivation (frame b t (t+1) (t+2) (t+3) 27 8).encode := by
    simpa [rename, show t ≠ 29 by omega, show (t+1) ≠ 29 by omega, show (t+2) ≠ 29 by omega, show 27 ≠ 29 by omega, show 8 ≠ 29 by omega] using
      instantiate_name b t (t+1) (t+2) 29 27 8 29 (t+3) (by omega) (by omega) h3
  have h5 : KDerivation (frame b t (t+1) (t+2) (t+3) (t+4) 8).encode := by
    simpa [rename, show t ≠ 27 by omega, show (t+1) ≠ 27 by omega, show (t+2) ≠ 27 by omega, show (t+3) ≠ 27 by omega, show 8 ≠ 27 by omega] using
      instantiate_name b t (t+1) (t+2) (t+3) 27 8 27 (t+4) (by omega) (by omega) h4
  have h6 : KDerivation (frame b t (t+1) (t+2) (t+3) (t+4) (t+5)).encode := by
    simpa [rename, show t ≠ 8 by omega, show (t+1) ≠ 8 by omega, show (t+2) ≠ 8 by omega, show (t+3) ≠ 8 by omega, show (t+4) ≠ 8 by omega] using
      instantiate_name b t (t+1) (t+2) (t+3) (t+4) 8 8 (t+5) (by omega) (by omega) h5
  have h7 : KDerivation (frame b x (t+1) (t+2) (t+3) (t+4) (t+5)).encode := by
    simpa [rename, show (t+1) ≠ t by omega, show (t+2) ≠ t by omega, show (t+3) ≠ t by omega, show (t+4) ≠ t by omega, show (t+5) ≠ t by omega] using
      instantiate_name b t (t+1) (t+2) (t+3) (t+4) (t+5) t x (by omega) (by omega) h6
  have h8 : KDerivation (frame b x y (t+2) (t+3) (t+4) (t+5)).encode := by
    simpa [rename, show x ≠ (t+1) by omega, show (t+2) ≠ (t+1) by omega, show (t+3) ≠ (t+1) by omega, show (t+4) ≠ (t+1) by omega, show (t+5) ≠ (t+1) by omega] using
      instantiate_name b x (t+1) (t+2) (t+3) (t+4) (t+5) (t+1) y (by omega) (by omega) h7
  have h9 : KDerivation (frame b x y z (t+3) (t+4) (t+5)).encode := by
    simpa [rename, show x ≠ (t+2) by omega, show y ≠ (t+2) by omega, show (t+3) ≠ (t+2) by omega, show (t+4) ≠ (t+2) by omega, show (t+5) ≠ (t+2) by omega] using
      instantiate_name b x y (t+2) (t+3) (t+4) (t+5) (t+2) z (by omega) (by omega) h8
  have h10 : KDerivation (frame b x y z u (t+4) (t+5)).encode := by
    simpa [rename, show x ≠ (t+3) by omega, show y ≠ (t+3) by omega, show z ≠ (t+3) by omega, show (t+4) ≠ (t+3) by omega, show (t+5) ≠ (t+3) by omega] using
      instantiate_name b x y z (t+3) (t+4) (t+5) (t+3) u (by omega) (by omega) h9
  have h11 : KDerivation (frame b x y z u v (t+5)).encode := by
    simpa [rename, show x ≠ (t+4) by omega, show y ≠ (t+4) by omega, show z ≠ (t+4) by omega, show u ≠ (t+4) by omega, show (t+5) ≠ (t+4) by omega] using
      instantiate_name b x y z u (t+4) (t+5) (t+4) v (by omega) (by omega) h10
  have h12 : KDerivation (frame b x y z u v w).encode := by
    simpa [rename, show x ≠ (t+5) by omega, show y ≠ (t+5) by omega, show z ≠ (t+5) by omega, show u ≠ (t+5) by omega, show v ≠ (t+5) by omega] using
      instantiate_name b x y z u v (t+5) (t+5) w (by omega) (by omega) h11
  exact h12

theorem congruence_at_high_base_certificate (x y z u v w : Nat) :
    theoremCode (certificate (congruence_at_high_base x y z u v w)) =
      (frame (highBase x y z u v w) x y z u v w).encode := certificate_correct _

end PASoundness.PAtoCompactAdditionCongruenceArbitraryLabels

#print axioms PASoundness.PAtoCompactAdditionCongruenceArbitraryLabels.temporary
#print axioms PASoundness.PAtoCompactAdditionCongruenceArbitraryLabels.highBase
#print axioms PASoundness.PAtoCompactAdditionCongruenceArbitraryLabels.congruence_at_high_base
#print axioms PASoundness.PAtoCompactAdditionCongruenceArbitraryLabels.congruence_at_high_base_certificate
