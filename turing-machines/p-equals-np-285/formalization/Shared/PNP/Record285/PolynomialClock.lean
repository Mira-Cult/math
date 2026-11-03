import Shared.PNP.Record285.ClockCoverage
import Shared.ComplexityBridge.ClockBounds

/-! Adapt the pinned library's natural-polynomial bounds to the source clock.
No canonical-model machine compiler or reference completeness is assumed here. -/
namespace Shared.PNP.Record285.PolynomialClock
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.ClockCoverage
open Shared.PNP.Record285.OrdinaryEncoding
open Shared.Beeping.Machines

/-- The canonical frame `1^n 0 payload` has length `2*n+1`. Its polynomial
time bound is dominated by a monomial in the source payload length. -/
theorem polynomial_frame_bound (p : Polynomial Nat) :
    ∃ a d : Nat, ∀ size, p.eval (2*size+1) ≤ a*(size+2)^d := by
  obtain ⟨d,h⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent p
  refine ⟨2^d,d,?_⟩
  intro size
  calc
    p.eval (2*size+1) ≤ ((2*size+1)+2)^d := h _
    _ ≤ (2*(size+2))^d := Nat.pow_le_pow_left (by omega) d
    _ = 2^d*(size+2)^d := Nat.mul_pow 2 (size+2) d

/-- Uniform source candidate and clock for an ordinary marked machine whose
completion time is bounded by a canonical `Polynomial Nat` evaluated at the
actual framed input length. -/
theorem finite_machine_canonical_polynomial_coverage
    (M : Machine states) (L : Nat → Nat → Prop) (bound : Polynomial Nat)
    (hsound : ∀ size payload, payload < 2^size → ∀ t,
      (loaded M (frame (2^size) payload)).BeepAt t → L size payload)
    (hcomplete : ∀ size payload, payload < 2^size → L size payload →
      ∃ t, t < bound.eval (2*size+1) ∧
        (loaded M (frame (2^size) payload)).BeepAt t) :
    ∃ program exponent, 0 < exponent ∧ ∀ size payload, payload < 2^size →
      (candidate program exponent size (2^size) payload = true ↔ L size payload) := by
  obtain ⟨a,d,hbound⟩ := polynomial_frame_bound bound
  apply finite_machine_coverage M L a 0 d hsound
  intro size payload hp hlanguage
  obtain ⟨t,ht,hevent⟩ := hcomplete size payload hp hlanguage
  refine ⟨t,?_,hevent⟩
  have h := hbound size
  omega

/-- A canonical-polynomial event decider for the exact bounded reference
suffices for eventual silence of the abstract source controller. -/
theorem source_silent_of_canonical_polynomial_machine
    (M : Machine states) (bound : Polynomial Nat)
    (hsound : ∀ size payload, payload < 2^size → ∀ t,
      (loaded M (frame (2^size) payload)).BeepAt t →
        reference size (2^size) payload = true)
    (hcomplete : ∀ size payload, payload < 2^size →
      reference size (2^size) payload = true →
      ∃ t, t < bound.eval (2*size+1) ∧
        (loaded M (frame (2^size) payload)).BeepAt t) :
    controller.EventuallySilent := by
  obtain ⟨program,exponent,hpos,hcorrect⟩ :=
    finite_machine_canonical_polynomial_coverage M
      (fun size payload => reference size (2^size) payload = true)
      bound hsound hcomplete
  apply eventuallySilent_iff_goodCandidate.mpr
  refine ⟨program,exponent,hpos,?_⟩
  intro size payload hbound
  have h := hcorrect size payload hbound
  unfold mismatch
  cases hc : candidate program exponent size (2^size) payload <;>
    cases hr : reference size (2^size) payload <;> simp_all

end Shared.PNP.Record285.PolynomialClock
