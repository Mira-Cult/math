import Shared.Beeping.NPcoNP.Source284GraphBothPhases

/-! The finite post-search comparison in the producer's register graph. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphComparison
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg cat)
abbrev Bank := PASoundness.RegisterMachine.Bank 12

def finishCost (ref cand : Bool) : Nat :=
  if cand then (if ref then 3 else 6) else (if ref then 3 else 2)

def finishBank (b : Bank) (ref cand : Bool) : Bank :=
  if !(ref == cand) then write (write b 0 1) 4 (b 4+1)
  else write (write b 0 0) 3 (b 3+1)

/-- The concrete graph toggles its reference bit on candidate acceptance,
then chooses continuation or rejection exactly as the source comparison does. -/
theorem finish (b : Bank) (ref cand : Bool) (h : b 0 = if ref then 1 else 0) :
    Seg ⟨if cand then 178 else 181,b⟩
      ⟨if !(ref == cand) then 2 else 0,finishBank b ref cand⟩ (finishCost ref cand) := by
  cases ref <;> cases cand <;>
    simp_all [Seg,finishCost,finishBank,WordEventSystem.advance,WordEventSystem.wordFrom,
      target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write]
  all_goals funext i; fin_cases i <;> simp [write,h]

/-- One complete source comparison finishes in positive finite time.
The graph reaches PC 2 for a successful test or PC 0 for a rejection;
PC 0 emits the next beep on its following transition. -/
theorem comparison_from_pc2 (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      Seg ⟨2,b⟩ ⟨if Source284Comparison.compare (b 3) (b 4) then 2 else 0,out⟩ time ∧
      out 3 = (if Source284Comparison.compare (b 3) (b 4) then b 3 else b 3+1) ∧
      out 4 = (if Source284Comparison.compare (b 3) (b 4) then b 4+1 else b 4) ∧
      out 9=0 ∧ out 10=0 ∧ out 11=0 := by
  obtain ⟨k,r,hk,ha,hw,h0,h3,h4,hs9,hs10,hs11⟩ :=
    Source284GraphBothPhases.both_from_pc2 b h9 h10 h11
  let ref := Source284Comparison.reference (b 4)
  let cand := Source284Comparison.candidate (b 3) (b 4)
  let out := finishBank r ref cand
  have hf := finish r ref cand (by simpa [ref] using h0)
  have hstart : Seg ⟨2,b⟩ ⟨if cand then 178 else 181,r⟩ k := by
    simpa [Seg,cand] using And.intro ha hw
  have hend : Seg ⟨if cand then 178 else 181,r⟩
      ⟨if Source284Comparison.compare (b 3) (b 4) then 2 else 0,out⟩ (finishCost ref cand) := by
    simpa [out,ref,cand,Source284Comparison.compare] using hf
  have hseg := cat hstart hend
  have hout3 : out 3 = (if Source284Comparison.compare (b 3) (b 4) then b 3 else b 3+1) := by
    by_cases he : Source284Comparison.reference (b 4) = Source284Comparison.candidate (b 3) (b 4) <;>
      simp [out,finishBank,ref,cand,Source284Comparison.compare,he,write,h3]
  have hout4 : out 4 = (if Source284Comparison.compare (b 3) (b 4) then b 4+1 else b 4) := by
    by_cases he : Source284Comparison.reference (b 4) = Source284Comparison.candidate (b 3) (b 4) <;>
      simp [out,finishBank,ref,cand,Source284Comparison.compare,he,write,h4]
  have hscratch : out 9=0 ∧ out 10=0 ∧ out 11=0 := by
    by_cases he : ref = cand <;> simp [out,finishBank,he,write,hs9,hs10,hs11]
  exact ⟨k+finishCost ref cand,out,by omega,hseg,hout3,hout4,hscratch.1,hscratch.2.1,hscratch.2.2⟩

end Shared.Beeping.NPcoNP.Source284GraphComparison
