import PASoundness.PAtoCompactAdditionOutputFrame

/-! Capture-safe reallocation of all four free names in the addition output
frame. The fixed-label K proof is supplied explicitly; no output law is
constructed by this module. -/
namespace PASoundness.PAtoCompactAdditionOutputSchedule
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdditionOutputFrame
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def temporary (x y q r : Nat) : Nat := max (max x y) (max q r) + 40
def highBase (x y q r : Nat) : Nat := temporary x y q r + 100

/-- An explicit proof at fixed names 30,31,32,8 transfers to arbitrary
free labels at one high allocator. Four distinct private temporaries prevent
capture even when any requested labels denote the same syntactic name or
object. The existence of the fixed-name proof remains a separate input. -/
def instantiate_at_high_base (x y q r : Nat)
    (h0 : KDerivation (frame (highBase x y q r) 30 31 32 8).encode) :
    KDerivation (frame (highBase x y q r) x y q r).encode := by
  let t := temporary x y q r
  let b := highBase x y q r
  have ht : 32 < t := by dsimp [t,temporary]; omega
  have hx : x < t := by dsimp [t,temporary]; omega
  have hy : y < t := by dsimp [t,temporary]; omega
  have hq : q < t := by dsimp [t,temporary]; omega
  have hr : r < t := by dsimp [t,temporary]; omega
  have htb : t + 3 < b := by dsimp [b,highBase,t]; omega
  have h1 : KDerivation (frame b t 31 32 8).encode := by
    simpa [rename] using instantiate_name b 30 31 32 8 30 t (by omega) (by omega) h0
  have h2 : KDerivation (frame b t (t+1) 32 8).encode := by
    simpa [rename, show t ≠ 31 by omega] using
      instantiate_name b t 31 32 8 31 (t+1) (by omega) (by omega) h1
  have h3 : KDerivation (frame b t (t+1) (t+2) 8).encode := by
    simpa [rename, show t ≠ 32 by omega, show t+1 ≠ 32 by omega] using
      instantiate_name b t (t+1) 32 8 32 (t+2) (by omega) (by omega) h2
  have h4 : KDerivation (frame b t (t+1) (t+2) (t+3)).encode := by
    simpa [rename, show t ≠ 8 by omega, show t+1 ≠ 8 by omega, show t+2 ≠ 8 by omega] using
      instantiate_name b t (t+1) (t+2) 8 8 (t+3) (by omega) (by omega) h3
  have h5 : KDerivation (frame b x (t+1) (t+2) (t+3)).encode := by
    simpa [rename, show t+1 ≠ t by omega, show t+2 ≠ t by omega, show t+3 ≠ t by omega] using
      instantiate_name b t (t+1) (t+2) (t+3) t x (by omega) (by omega) h4
  have h6 : KDerivation (frame b x y (t+2) (t+3)).encode := by
    simpa [rename, show x ≠ t+1 by omega, show t+2 ≠ t+1 by omega, show t+3 ≠ t+1 by omega] using
      instantiate_name b x (t+1) (t+2) (t+3) (t+1) y (by omega) (by omega) h5
  have h7 : KDerivation (frame b x y q (t+3)).encode := by
    simpa [rename, show x ≠ t+2 by omega, show y ≠ t+2 by omega, show t+3 ≠ t+2 by omega] using
      instantiate_name b x y (t+2) (t+3) (t+2) q (by omega) (by omega) h6
  have h8 : KDerivation (frame b x y q r).encode := by
    simpa [rename, show x ≠ t+3 by omega, show y ≠ t+3 by omega, show q ≠ t+3 by omega] using
      instantiate_name b x y q (t+3) (t+3) r (by omega) (by omega) h7
  exact h8

theorem instantiate_at_high_base_certificate (x y q r : Nat)
    (h0 : KDerivation (frame (highBase x y q r) 30 31 32 8).encode) :
    theoremCode (certificate (instantiate_at_high_base x y q r h0)) =
      (frame (highBase x y q r) x y q r).encode := certificate_correct _
end PASoundness.PAtoCompactAdditionOutputSchedule

#print axioms PASoundness.PAtoCompactAdditionOutputSchedule.instantiate_at_high_base
#print axioms PASoundness.PAtoCompactAdditionOutputSchedule.instantiate_at_high_base_certificate
