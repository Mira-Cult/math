import Shared.Beeping.NPcoNP.Source284GraphCandidateBranch
import Shared.Beeping.NPcoNP.Source284GraphCandidateInputCopy
import Shared.Beeping.NPcoNP.Source284GraphCandidateClockCopy
import Shared.Beeping.NPcoNP.Source284GraphCandidateAttempt

/-! Candidate witness selection and evaluator initialization in the parsed
register graph. This does not assert reachability from a blank physical tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateSetup
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg cat)
open Shared.Beeping.NPcoNP.Source284GraphParserInit (clear_loop)
abbrev Bank := PASoundness.RegisterMachine.Bank 12
abbrev IC := Source284GraphCandidateInputCopy.bank
abbrev CC := Source284GraphCandidateClockCopy.bank

/-- Copy the input from register 4 to register 1 while restoring register 4. -/
theorem input_copy (b : Bank) (h9 : b 9=0) (h10 : b 10=0) :
    Seg ⟨124,b⟩ ⟨132,IC b (b 4) (b 4) 0 0⟩ (7*b 4+b 1+4) := by
  let x := b 4
  let y := b 1
  have hb : IC b x y 0 0 = b := by
    simpa [IC,x,y,h9,h10] using Source284GraphCandidateInputCopy.bank_same b
  have h1 : Seg ⟨124,IC b x y 0 0⟩ ⟨127,IC b 0 y x x⟩ (3*x+1) := by
    simpa [Seg,IC] using Source284GraphCandidateInputCopy.drain b x y 0 0
  have h2 : Seg ⟨127,IC b 0 y x x⟩ ⟨129,IC b x y 0 x⟩ (2*x+1) := by
    simpa [Seg,IC] using Source284GraphCandidateInputCopy.restore b 0 y x x
  have h3 : Seg ⟨129,IC b x y 0 x⟩ ⟨130,IC b x 0 0 x⟩ (y+1) := by
    simpa [Seg,IC] using Source284GraphCandidateInputCopy.clear b x y 0 x
  have h4 : Seg ⟨130,IC b x 0 0 x⟩ ⟨132,IC b x x 0 0⟩ (2*x+1) := by
    simpa [Seg,IC] using Source284GraphCandidateInputCopy.place b x 0 0 x
  have ht : 7*x+y+4 = (((3*x+1)+(2*x+1))+(y+1))+(2*x+1) := by omega
  have hh := cat (cat (cat h1 h2) h3) h4
  simpa only [ht,hb,x,y] using hh

theorem row132 (b : Bank) : target.system.step ⟨132,b⟩ =
    if b 2 = 0 then (⟨133,b⟩,[]) else (⟨132,write b 2 (b 2-1)⟩,[]) := by
  cases h : b (2 : Fin 12) <;>
    simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,h,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix]

theorem row133 (b : Bank) : target.system.step ⟨133,b⟩ = (⟨134,write b 2 (b 2+1)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix]

/-- The bank after witness selection and preparation for bounded evaluation. -/
def ready (b : Bank) : Bank :=
  let cert := b 7-1
  write (write (write (write (write b 7 cert) 8 cert) 1 (b 4)) 2 1) 11 (b 6)

def setupCost (b : Bank) : Nat :=
  (7*(b 7-1)+b 8+5) + (7*b 4+b 1+4) + (b 2+1) + 1 + (7*b 6+3)

/-- Positive witness counters reach the standard candidate evaluator input
in a finite, silent graph segment. -/
theorem setup (b : Bank) (h7 : 0 < b 7)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    0 < setupCost b ∧ Seg ⟨115,b⟩ ⟨141,ready b⟩ (setupCost b) := by
  let m := b 7-1
  let mid := Source284GraphCandidateBranch.bank b m m 0 0
  let copied := IC mid (mid 4) (mid 4) 0 0
  let cleared := write copied 2 0
  let set := write copied 2 1
  have hbranch := Source284GraphCandidateBranch.branch_nonzero b h7 h9 h10
  have hm9 : mid 9=0 := by simp [mid,Source284GraphCandidateBranch.bank]
  have hm10 : mid 10=0 := by simp [mid,Source284GraphCandidateBranch.bank]
  have hi := input_copy mid hm9 hm10
  have hclear := clear_loop target.system 132 133 2 row132 copied
  have hset : Seg ⟨133,cleared⟩ ⟨134,set⟩ 1 := by
    have hw : write cleared 2 (cleared 2+1)=set := by
      funext i; fin_cases i <;> simp [cleared,set,write]
    simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row133,hw]
  have hc := Source284GraphCandidateClockCopy.copy_segment set (set 6) 0 0 0
  have hs9 : set 9=0 := by simp [set,copied,IC,Source284GraphCandidateInputCopy.bank,write]
  have hs10 : set 10=0 := by simp [set,copied,IC,Source284GraphCandidateInputCopy.bank,write]
  have hs11 : set 11=0 := by simp [set,copied,IC,mid,Source284GraphCandidateInputCopy.bank,
    Source284GraphCandidateBranch.bank,h11,write]
  have hc0 : CC set (set 6) 0 0 0 = set := by
    simpa [CC,hs9,hs10,hs11] using Source284GraphCandidateClockCopy.bank_same set
  have hout : CC set (set 6) 0 0 (set 6) = ready b := by
    funext i
    fin_cases i <;> simp [CC,set,copied,IC,mid,m,ready,
      Source284GraphCandidateClockCopy.bank,Source284GraphCandidateInputCopy.bank,
      Source284GraphCandidateBranch.bank,write,h9,h10,h11]
  have hclock : Seg ⟨134,set⟩ ⟨141,ready b⟩ (7*b 6+3) := by
    have hv : set 6=b 6 := by simp [set,copied,IC,mid,Source284GraphCandidateInputCopy.bank,
      Source284GraphCandidateBranch.bank,write]
    change CC set (set 6) 0 0 0 = set at hc0
    change CC set (set 6) 0 0 (set 6) = ready b at hout
    simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add] at hc
    change target.system.advance ⟨134,CC set (set 6) 0 0 0⟩ _ = _ ∧ _ at hc
    rw [hv] at hc0 hout hc
    simpa only [Seg,hout,hc0] using hc
  have hbranch' : Seg ⟨115,b⟩ ⟨124,mid⟩ (7*m+b 8+5) := by
    simpa [Seg,mid,m,Source284GraphCandidateBranch.SilentSegment] using hbranch.2
  have hcopy : Seg ⟨124,mid⟩ ⟨132,copied⟩ (7*b 4+b 1+4) := by
    simpa [mid,Source284GraphCandidateBranch.bank,copied,IC,write] using hi
  have hclear' : Seg ⟨132,copied⟩ ⟨133,cleared⟩ (b 2+1) := by
    simpa [Seg,cleared,copied,IC,mid,Source284GraphCandidateInputCopy.bank,
      Source284GraphCandidateBranch.bank] using hclear
  have hall := cat (cat (cat (cat hbranch' hcopy) hclear') hset) hclock
  refine ⟨by unfold setupCost; omega,?_⟩
  simpa only [setupCost,m] using hall

end Shared.Beeping.NPcoNP.Source284GraphCandidateSetup
