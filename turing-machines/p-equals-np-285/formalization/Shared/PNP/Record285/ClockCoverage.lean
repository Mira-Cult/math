import Shared.PNP.Record285.OrdinaryEncoding
import Shared.PNP.Record285.SourceEndpoint

/-! Uniform source candidate and adequate clock for a finite ordinary marked
machine with a supplied polynomial event bound. This theorem does not supply
the canonical-model-to-binary-machine compiler or prove reference hardness. -/
namespace Shared.PNP.Record285.ClockCoverage
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.OrdinaryEncoding
open Shared.Beeping.Machines

/-- Any constant is bounded by the corresponding power of a base at least 2. -/
theorem le_power_self (base k : Nat) (hbase : 2 ≤ base) : k ≤ base^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 1 ≤ base^k := Nat.one_le_pow k base (by omega)
    calc
      k+1 ≤ base^k + base^k := by omega
      _ = 2 * base^k := by omega
      _ ≤ base * base^k := Nat.mul_le_mul_right (base^k) hbase
      _ = base^(k+1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- A fixed polynomial of the form `a*(n+2)^d+b` is dominated by one
positive-exponent source clock, uniformly including `n = 0`. -/
theorem polynomial_le_clock (a b d size : Nat) :
    a * (size+2)^d + b ≤ (size+2)^(d+(a+b)+1) := by
  let base := size+2
  have hb : 2 ≤ base := by dsimp [base]; omega
  have hp : 1 ≤ base^d := Nat.one_le_pow d base (by omega)
  have hmul : b ≤ b * base^d := by
    have h := Nat.mul_le_mul_left b hp
    simpa using h
  have hc := le_power_self base (a+b) hb
  change a * base^d + b ≤ base^(d+(a+b)+1)
  calc
    a * base^d + b ≤ a * base^d + b * base^d := Nat.add_le_add_left hmul _
    _ = (a+b)*base^d := by rw [Nat.add_mul]
    _ ≤ base^(a+b)*base^d := Nat.mul_le_mul_right _ hc
    _ = base^(d+(a+b)) := by
      simp only [Nat.pow_add]
      ac_rfl
    _ ≤ base^(d+(a+b)+1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Evaluate a finite list of natural coefficients, low degree first. -/
def evalCoefficients : List Nat → Nat → Nat
  | [], _ => 0
  | a :: rest, x => a + x * evalCoefficients rest x

/-- Every such polynomial is bounded by coefficient sum times one power. -/
theorem coefficients_le_monomial (coefficients : List Nat) (size : Nat) :
    evalCoefficients coefficients size ≤ coefficients.sum * (size+2)^coefficients.length := by
  induction coefficients with
  | nil => simp [evalCoefficients]
  | cons a rest ih =>
    have hbase : 0 < size+2 := by omega
    have hp : 1 ≤ (size+2)^(rest.length+1) := Nat.one_le_pow _ _ hbase
    have ha : a ≤ a*(size+2)^(rest.length+1) := by
      have h := Nat.mul_le_mul_left a hp
      simpa using h
    have hr : size * evalCoefficients rest size ≤
        (size+2) * (rest.sum*(size+2)^rest.length) :=
      Nat.mul_le_mul (by omega) ih
    calc
      evalCoefficients (a::rest) size = a + size*evalCoefficients rest size := rfl
      _ ≤ a*(size+2)^(rest.length+1) +
          (size+2)*(rest.sum*(size+2)^rest.length) := Nat.add_le_add ha hr
      _ = a*(size+2)^(rest.length+1) + rest.sum*(size+2)^(rest.length+1) := by
        congr 1
        rw [Nat.pow_succ]
        ac_rfl
      _ = (a::rest).sum * (size+2)^(a::rest).length := by
        simp only [List.sum_cons, List.length_cons]
        rw [Nat.add_mul]

/-- Uniform program-and-clock coverage for an ordinary machine with sound
marked events and polynomially bounded events on positive instances. The
hypotheses quantify over every valid source payload; no P = NP assumption is
used. The remaining model bridge must supply such a machine for canonical
polynomial-time deciders. -/
theorem finite_machine_coverage (M : Machine states) (L : Nat → Nat → Prop)
    (a b d : Nat)
    (hsound : ∀ size payload, payload < 2^size → ∀ t,
      (loaded M (frame (2^size) payload)).BeepAt t → L size payload)
    (hcomplete : ∀ size payload, payload < 2^size → L size payload →
      ∃ t, t < a*(size+2)^d+b ∧
        (loaded M (frame (2^size) payload)).BeepAt t) :
    ∃ program exponent, 0 < exponent ∧ ∀ size payload, payload < 2^size →
      (candidate program exponent size (2^size) payload = true ↔ L size payload) := by
  refine ⟨finiteProgram (2*states) (table (normalized M)), d+(a+b)+1, by omega, ?_⟩
  intro size payload hbound
  rw [arbitrary_candidate_iff_loaded_event]
  constructor
  · rintro ⟨t,_,hevent⟩
    exact hsound size payload hbound t hevent
  · intro hlanguage
    obtain ⟨t,ht,hevent⟩ := hcomplete size payload hbound hlanguage
    exact ⟨t, Nat.lt_of_lt_of_le ht (polynomial_le_clock a b d size), hevent⟩

/-- The same coverage result for an arbitrary finite natural coefficient
list, with a uniform source exponent derived from that list. -/
theorem finite_machine_polynomial_coverage (M : Machine states) (L : Nat → Nat → Prop)
    (coefficients : List Nat)
    (hsound : ∀ size payload, payload < 2^size → ∀ t,
      (loaded M (frame (2^size) payload)).BeepAt t → L size payload)
    (hcomplete : ∀ size payload, payload < 2^size → L size payload →
      ∃ t, t < evalCoefficients coefficients size ∧
        (loaded M (frame (2^size) payload)).BeepAt t) :
    ∃ program exponent, 0 < exponent ∧ ∀ size payload, payload < 2^size →
      (candidate program exponent size (2^size) payload = true ↔ L size payload) := by
  apply finite_machine_coverage M L coefficients.sum 0 coefficients.length hsound
  intro size payload hbound hlanguage
  obtain ⟨t,ht,hevent⟩ := hcomplete size payload hbound hlanguage
  refine ⟨t,?_,hevent⟩
  have hb := coefficients_le_monomial coefficients size
  omega

/-- If a finite ordinary marked machine decides this exact bounded reference
with a polynomial event bound, the abstract source controller eventually
falls silent. The ordinary-machine and bound hypotheses remain explicit. -/
theorem source_silent_of_reference_machine (M : Machine states) (coefficients : List Nat)
    (hsound : ∀ size payload, payload < 2^size → ∀ t,
      (loaded M (frame (2^size) payload)).BeepAt t →
        reference size (2^size) payload = true)
    (hcomplete : ∀ size payload, payload < 2^size →
      reference size (2^size) payload = true →
      ∃ t, t < evalCoefficients coefficients size ∧
        (loaded M (frame (2^size) payload)).BeepAt t) :
    controller.EventuallySilent := by
  obtain ⟨program,exponent,hpos,hcorrect⟩ :=
    finite_machine_polynomial_coverage M
      (fun size payload => reference size (2^size) payload = true)
      coefficients hsound hcomplete
  apply eventuallySilent_iff_goodCandidate.mpr
  refine ⟨program,exponent,hpos,?_⟩
  intro size payload hbound
  have h := hcorrect size payload hbound
  unfold mismatch
  cases hc : candidate program exponent size (2^size) payload <;>
    cases hr : reference size (2^size) payload <;> simp_all

end Shared.PNP.Record285.ClockCoverage
