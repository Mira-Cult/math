import Shared.PNP.Record285.CleanBank
import Shared.PNP.Record285.InitializationComplete

/-! Bind the blank-start initialization to the common full-tape clean-bank
invariant. This is not yet a proof that all subsequent actions preserve their
control-layout premises. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 8192

namespace Shared.PNP.Record285.CleanBank
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.InitializationComposition

theorem zero_blocks_rep4 (n : Nat) :
    IncrementSelector.blocksBits (List.replicate n 0) 0 = rep4 n := by
  induction n with
  | zero => simp [IncrementSelector.blocksBits,rep4]
  | succ n ih =>
    simp only [List.replicate_succ,IncrementSelector.blocksBits,runPattern,bitVal,
      Bool.false_eq_true,if_false,Nat.zero_add,ih,rep4_succ]
    omega

theorem candidate_clean_numeric : candidate =
    denote (rightWord treeRoot 0 [] false rootLeft [false]) (-3818) 0
      (runPattern false 3819 true
        (2*IncrementSelector.blocksBits (List.replicate 1909 0) 0)) := by
  rw [zero_blocks_rep4,runPattern_closed]
  have hr : 1+4*rep4 1909 = rep4 1910 := by
    simpa only [Nat.mul_comm,Nat.add_comm] using (rep4_succ 1909).symm
  have hp : 2*2^3819 = 4^1910 := by decide
  simp only [candidate,rightWord,denote,rootLeft,treeRoot,bits,List.replicate_succ,
    List.replicate_zero,bitVal,Bool.false_eq_true,if_false,if_true,Nat.zero_mul,Nat.zero_add,
    Int.add_zero]
  have hb : 1+2*(2*rep4 1909) = rep4 1910 := by omega
  rw [hb]
  rw [← Nat.mul_assoc,hp]
  rfl

/-- The machine reaches the clean-root invariant from the wholly blank tape,
with its original 1,909 explicitly represented zero-valued bank fields. -/
theorem blank_start_reaches_clean_root :
    Root (List.replicate 1909 0) (Record285.machine.system.run 89806142) ∧
      ∀ t, t < 89806142 → ¬ Record285.machine.system.BeepAt t := by
  refine ⟨⟨[],false,-3818,0,3819,?_⟩,InitializationComplete.blank_start_entry.2⟩
  change Rel (denote (rightWord treeRoot 0 [] false rootLeft [false]) (-3818) 0
    (runPattern false 3819 true (2*IncrementSelector.blocksBits (List.replicate 1909 0) 0))) _
  rw [← candidate_clean_numeric]
  exact InitializationComplete.blank_start_entry.1

end Shared.PNP.Record285.CleanBank
