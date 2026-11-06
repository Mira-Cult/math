import Shared.Beeping.NPcoNP.Source284CheckpointWorkspace

/-! Quantitative separation of the physically retained guard-token block
from the later workspace block. Both stage counts are fixed before the
source execution. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointGrowth

open Shared.Beeping.NPcoNP.Source284ProductIteration
open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace

theorem blocks_at_least_two (k a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2 ≤ outerAfter k a b ∧ 2 ≤ innerAfter k a b := by
  induction k generalizing a b with
  | zero => simpa [outerAfter,innerAfter] using And.intro ha hb
  | succ k ih =>
    have hab : 2 ≤ a*b := by
      have h := Nat.mul_le_mul ha hb
      omega
    simpa [outerAfter,innerAfter] using ih b (a*b) hb hab

theorem checkpoint_blocks (k n : Nat) : 2 ≤ previous k n ∧ 2 ≤ guard k n := by
  exact blocks_at_least_two k (base n) (base n) (by simp [base]) (by simp [base])

/-- Two stages make both current blocks at least `b`; further fixed stages
then dominate any fixed polynomial in the original guard length. -/
theorem extra_stages_dominate (p : Polynomial Nat) :
    ∃ r : Nat, ∀ (a b : Nat), 1 ≤ a → 2 ≤ b → p.eval b ≤ innerAfter (r+2) a b := by
  obtain ⟨e,he⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent p
  refine ⟨2*e,?_⟩
  intro a b ha hb
  have hbase : b+2 ≤ b*b := by nlinarith
  have hpower := Nat.pow_le_pow_left hbase e
  have hp : (b*b)^e = b^(2*e) := by rw [← pow_two,pow_mul]
  rw [hp] at hpower
  have hab : b ≤ a*b := by
    calc
      b = 1*b := by simp
      _ ≤ a*b := Nat.mul_le_mul_right b ha
  have hlarge : b ≤ b*(a*b) := by
    have hpos : 1 ≤ a*b := by omega
    calc
      b = b*1 := by simp
      _ ≤ b*(a*b) := Nat.mul_le_mul_left b hpos
  have hfactor : 1 ≤ b*(a*b) := by omega
  have hlower := Source284ProductGrowth.inner_lower (2*e) b (a*b) (b*(a*b)) (by omega) hab hlarge
  have hmult : b^(2*e) ≤ (b*(a*b))*b^(2*e) := by
    calc
      b^(2*e) = 1*b^(2*e) := by simp
      _ ≤ (b*(a*b))*b^(2*e) := Nat.mul_le_mul_right _ hfactor
  have hrec : innerAfter (2*e+2) a b = innerAfter (2*e) (a*b) (b*(a*b)) := by
    simp [innerAfter]
  rw [hrec]
  exact le_trans (he b) (le_trans hpower (le_trans hmult hlower))

/-- One fixed number of extra stages makes the workspace dominate any
polynomial of the retained guard length, uniformly in the original stage
count and input length. -/
theorem workspace_dominates_guard (p : Polynomial Nat) :
    ∃ r : Nat, ∀ (k n : Nat), p.eval (guard k n) ≤ workspace k r n := by
  obtain ⟨r,hr⟩ := extra_stages_dominate p
  refine ⟨r,?_⟩
  intro k n
  obtain ⟨ha,hb⟩ := checkpoint_blocks k n
  exact hr (previous k n) (guard k n) (by omega) hb

/-- The retained input-side scratch suffix contains the complete workspace
as a blank prefix, irrespective of the original input's high suffix. -/
theorem retained_zero (k r n suffix depth : Nat) (h : depth ≤ workspace k r n+1) :
    2^depth ∣ retained k r n suffix := by
  unfold retained
  have hpow : 2^depth ∣ 2^(workspace k r n+1) := Nat.pow_dvd_pow 2 h
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpow _) _) _

namespace Fixtures
/-- Empty input still seeds positive guard and independently larger
workspace blocks. The original certificate survives the checkpoint. -/
example : guard 0 0 = 2 ∧ workspace 0 0 0 = 8 ∧
    recoverCertificate 0 0 (checkpointHistory 0 0 173) = 173 := by decide +kernel

/-- Two more fixed growth stages enlarge the workspace while retaining the
same guard block. -/
example : guard 1 1 = 9 ∧ workspace 1 2 1 = 1594323 := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284CheckpointGrowth
