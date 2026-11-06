import Shared.Beeping.NPcoNP.Source284CheckpointGrowth

/-! Polynomial transition bounds and simultaneous guard/workspace
domination for the fixed-stage checkpoint source program. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointCost

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
open Shared.Beeping.NPcoNP.Source284ProductIteration

noncomputable def basePolynomial : Polynomial Nat := Polynomial.X+2
noncomputable def widthPolynomial : Polynomial Nat := Polynomial.X+1
noncomputable def previousPolynomial (k : Nat) : Polynomial Nat :=
  Source284ProductIterationPolynomial.outerPolynomial k basePolynomial basePolynomial
noncomputable def guardPolynomial (k : Nat) : Polynomial Nat :=
  Source284ProductIterationPolynomial.innerPolynomial k basePolynomial basePolynomial
noncomputable def workspacePolynomial (k r : Nat) : Polynomial Nat :=
  Source284ProductIterationPolynomial.innerPolynomial (r+2) (previousPolynomial k) (guardPolynomial k)
noncomputable def outerPolynomial (k r : Nat) : Polynomial Nat :=
  Source284ProductIterationPolynomial.outerPolynomial (r+2) (previousPolynomial k) (guardPolynomial k)
noncomputable def zerosPolynomial (k r : Nat) : Polynomial Nat :=
  2*(workspacePolynomial k r+1)+2*outerPolynomial k r
noncomputable def extraOuterPolynomial (k : Nat) : Polynomial Nat := previousPolynomial k*guardPolynomial k
noncomputable def extraInnerPolynomial (k : Nat) : Polynomial Nat := guardPolynomial k*extraOuterPolynomial k

theorem base_eval (n : Nat) : basePolynomial.eval n = base n := by simp [basePolynomial,base]
theorem width_eval (w : List Bool) : widthPolynomial.eval w.length = (w++[false]).length := by simp [widthPolynomial]

theorem previous_eval (k n : Nat) : (previousPolynomial k).eval n = previous k n := by
  have h := Source284ProductIterationPolynomial.outer_eval k n basePolynomial basePolynomial
  simpa [previousPolynomial,previous,base_eval] using h

theorem guard_eval (k n : Nat) : (guardPolynomial k).eval n = guard k n := by
  have h := Source284ProductIterationPolynomial.inner_eval k n basePolynomial basePolynomial
  simpa [guardPolynomial,Source284CheckpointWorkspace.guard,base_eval] using h

theorem workspace_eval (k r n : Nat) : (workspacePolynomial k r).eval n = workspace k r n := by
  have h := Source284ProductIterationPolynomial.inner_eval (r+2) n (previousPolynomial k) (guardPolynomial k)
  simpa [workspacePolynomial,workspace,previous_eval,guard_eval] using h

theorem outer_eval (k r n : Nat) : (outerPolynomial k r).eval n = workspaceOuter k r n := by
  have h := Source284ProductIterationPolynomial.outer_eval (r+2) n (previousPolynomial k) (guardPolynomial k)
  simpa [outerPolynomial,workspaceOuter,previous_eval,guard_eval] using h

theorem zeros_eval (k r n : Nat) : (zerosPolynomial k r).eval n = cleanupZeros k r n := by
  simp [zerosPolynomial,cleanupZeros,Polynomial.eval_add,Polynomial.eval_mul,workspace_eval,outer_eval]

theorem extraOuter_eval (k n : Nat) : (extraOuterPolynomial k).eval n = extraOuter k n := by
  simp [extraOuterPolynomial,extraOuter,Polynomial.eval_mul,previous_eval,guard_eval]

theorem extraInner_eval (k n : Nat) : (extraInnerPolynomial k).eval n = extraInner k n := by
  simp [extraInnerPolynomial,extraInner,Polynomial.eval_mul,guard_eval,extraOuter_eval]

noncomputable def costPolynomial (k r : Nat) : Polynomial Nat :=
  Source284SentinelPositiveTokens.costPolynomial+
    Source284ProductIteration.costPolynomial k basePolynomial basePolynomial widthPolynomial+
    Source284ProductIteration.costPolynomial (r+2) (previousPolynomial k) (guardPolynomial k) widthPolynomial+
    Source284PositivePolynomialTwoSided.workspacePolynomial (workspacePolynomial k r) widthPolynomial+
    ((zerosPolynomial k r+1)*(8*widthPolynomial+11)+(8*widthPolynomial+13))+
    Source284EraseTokenHistory.costPolynomial r (extraOuterPolynomial k) (extraInnerPolynomial k) widthPolynomial

/-- Every bootstrap, both product-stage groups, workspace operation and
partial cleanup is charged by one polynomial for the fixed program. -/
theorem totalCost_polynomial (k r : Nat) (w : List Bool) :
    totalCost k r w ≤ (costPolynomial k r).eval w.length := by
  have hinit := Source284SentinelPositiveTokens.totalCost_polynomial w
  have hfirst := Source284ProductIteration.cost_polynomial k w.length (base w.length) (base w.length)
    (w++[false]).length basePolynomial basePolynomial widthPolynomial
    (by simp [base_eval]) (by simp [base_eval]) (by simp [width_eval])
  have hextra := Source284ProductIteration.cost_polynomial (r+2) w.length (previous k w.length) (guard k w.length)
    (w++[false]).length (previousPolynomial k) (guardPolynomial k) widthPolynomial
    (by simp [previous_eval]) (by simp [guard_eval]) (by simp [width_eval])
  have hwork : (Source284PositivePolynomialTwoSided.workspacePolynomial
      (workspacePolynomial k r) widthPolynomial).eval w.length =
      Source284TwoSidedWorkspace.workCost (workspace k r w.length) (w++[false]).length := by
    simp [Source284PositivePolynomialTwoSided.workspacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      workspace_eval,width_eval,Source284TwoSidedWorkspace.workCost_formula]
  have hzero : (((zerosPolynomial k r+1)*(8*widthPolynomial+11)+(8*widthPolynomial+13))).eval w.length =
      Source284EraseZeroBlock.cost (cleanupZeros k r w.length) (w++[false]).length := by
    simp [Source284EraseZeroBlock.cost,Polynomial.eval_add,Polynomial.eval_mul,zeros_eval,width_eval]
  have hhistory := Source284EraseTokenHistory.costPolynomial_eval r w.length
    (extraOuterPolynomial k) (extraInnerPolynomial k) widthPolynomial
  rw [extraOuter_eval,extraInner_eval,width_eval] at hhistory
  simp only [costPolynomial,Polynomial.eval_add,hwork,hzero,hhistory]
  unfold totalCost
  omega

/-- The exact source handoff contains the original arbitrary certificate.
The extraction is a mathematical check, not an uncharged runtime step. -/
theorem source_certificate_recoverable (k r states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    recoverCertificate k w.length
      ((Source284Relative.run (description k r states continuation)
        (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k r w)).left) = certificate := by
  have h := Source284CheckpointWorkspace.source_then k r states continuation w certificate suffix 0 hn hv
  have hrun : Source284Relative.run (description k r states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k r w) =
      ⟨checkpointHistory k w.length certificate,2*flipped (w++[false]) (retained k r w.length suffix),
        active (1252+287*k+317*r)⟩ := by
    simpa [run,shiftConfig,toSource,nextState,active] using h
  rw [hrun]
  exact recover_checkpoint_certificate k w.length certificate

/-- Both quantities are selected before execution. The exact paid source
run retains the guard block and original certificate while the input-side
scratch suffix has a zero prefix large enough for the requested polynomial
of the guard size. -/
theorem source_polynomial_separation (guardDemand workspaceDemand : Polynomial Nat)
    (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k r : Nat, ∀ (w : List Bool) (certificate suffix : Nat),
      guardDemand.eval w.length ≤ guard k w.length ∧
      workspaceDemand.eval (guard k w.length) ≤ workspace k r w.length ∧
      2^(workspaceDemand.eval (guard k w.length)) ∣ retained k r w.length suffix ∧
      totalCost k r w ≤ (costPolynomial k r).eval w.length ∧
      Source284Relative.run (description k r states continuation)
        (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k r w) =
      ⟨checkpointHistory k w.length certificate,2*flipped (w++[false]) (retained k r w.length suffix),
        active (1252+287*k+317*r)⟩ := by
  obtain ⟨k,hk⟩ := Source284PositivePolynomialRunway.block_dominates guardDemand
  obtain ⟨r,hr⟩ := Source284CheckpointGrowth.workspace_dominates_guard workspaceDemand
  refine ⟨k,r,?_⟩
  intro w certificate suffix
  have hg : guardDemand.eval w.length ≤ guard k w.length := by
    simpa [Source284CheckpointWorkspace.guard,base,Source284PositivePolynomialRunway.block] using hk w.length
  have hw := hr k w.length
  refine ⟨hg,hw,Source284CheckpointGrowth.retained_zero k r w.length suffix _ (by omega),
    totalCost_polynomial k r w,?_⟩
  have h := Source284CheckpointWorkspace.source_then k r states continuation w certificate suffix 0 hn hv
  simpa [run,shiftConfig,toSource,nextState,active] using h

end Shared.Beeping.NPcoNP.Source284CheckpointCost
