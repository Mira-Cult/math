import Shared.Beeping.NPcoNP.Source284GraphReferenceSearch
import Shared.Beeping.NPcoNP.Source284GraphReferenceSetup
import Shared.Beeping.NPcoNP.Source284Comparison

/-! Complete source-reference evaluation on the pinned parsed register graph.
This starts from a supplied PC-2 bank, not from the physical blank tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphReferenceComplete
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphReferenceAttempt
open Shared.Beeping.NPcoNP.Source284GraphReferenceBounded
open Shared.Beeping.NPcoNP.Source284GraphReferenceSearch
open Shared.Beeping.NPcoNP.Source284GraphReferenceSetup
open Shared.Beeping.NPcoNP.Source284GraphParserTotal (header)
abbrev Bank := PASoundness.RegisterMachine.Bank 12

@[simp] theorem final4 (b : Bank) : finalBank b 4 = b 4 := by
  simp [finalBank,regs,ready,write]

@[simp] theorem final0 (b : Bank) : finalBank b 0 = b 0 := by
  simp [finalBank,regs,ready,write]

@[simp] theorem final3 (b : Bank) : finalBank b 3 = b 3 := by
  simp [finalBank,regs,ready,write]

theorem searchBank_three (b : Bank) (n : Nat) : searchBank b n 3 = b 3 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [searchBank]
    split
    · exact final3 b
    · rw [ih,final3]

theorem searchBank_five (b : Bank) (n : Nat) : searchBank b n 5 = b 5 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [searchBank]
    split
    · exact final5 b
    · rw [ih,final5]

theorem searchBank_scratch (b : Bank) (n : Nat)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    searchBank b n 9 = 0 ∧ searchBank b n 10 = 0 ∧ searchBank b n 11 = 0 := by
  induction n generalizing b with
  | zero => exact ⟨h9,h10,h11⟩
  | succ n ih =>
    simp only [searchBank]
    split
    · exact ⟨final9 b,final10 b,final11 b⟩
    · exact ih (finalBank b) (final9 b) (final10 b) (final11 b)

theorem searchBank_zero (b : Bank) (n : Nat) : searchBank b n 0 = b 0 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [searchBank]
    split
    · exact final0 b
    · rw [ih,final0]

/-- The descending search preserves the complete original input. -/
theorem searchBank_input (b : Bank) (n : Nat) : searchBank b n 4 = b 4 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [searchBank]
    split
    · exact final4 b
    · rw [ih,final4]

theorem ready_registers (b : Bank) :
    readyBank b 5 = Source284Parser.length (b 4) ∧
    readyBank b 6 = Source284Parser.description (b 4) ∧
    readyBank b 7 = Source284Parser.description (b 4) ∧
    readyBank b 9 = b 9 ∧ readyBank b 10 = b 10 ∧ readyBank b 11 = b 11 ∧
    readyBank b 4 = b 4 := by
  simp [readyBank,parsedBank,header,write]

/-- Candidate-phase registers that the complete reference phase preserves
or prepares, including the scratch cells required by the next computation. -/
def CandidateHandoff (b out : Bank) : Prop :=
  out 4 = b 4 ∧ out 3 = b 3 ∧ out 5 = Source284Parser.length (b 4) ∧
    out 9 = 0 ∧ out 10 = 0 ∧ out 11 = 0

/-- Parse the complete raw input and run every required reference-certificate
attempt. The result branch is exactly the source reference Boolean. The
original input is preserved, all transitions are finite, and no event is
emitted during this segment. -/
theorem reference_from_pc2 (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      target.system.advance ⟨2,b⟩ time =
        ⟨if Source284Comparison.reference (b 4) then 87 else 89,out⟩ ∧
      target.system.wordFrom ⟨2,b⟩ time = [] ∧ CandidateHandoff b out ∧ out 0 = 0 := by
  obtain ⟨k,hk,hsetup,wsetup⟩ := reference_setup b h9 h10
  let start := readyBank b
  let n := Source284Parser.description (b 4)
  have hr := ready_registers b
  have h7 : start 7 = n := by simpa [start,n] using hr.2.2.1
  have hs9 : start 9=0 := by simpa [start,h9] using hr.2.2.2.1
  have hs10 : start 10=0 := by simpa [start,h10] using hr.2.2.2.2.1
  have hs11 : start 11=0 := by simpa [start,h11] using hr.2.2.2.2.2.1
  have hsearch := search start n h7 hs9 hs10 hs11
  let out := searchBank start n
  have hout : out 4 = b 4 := by simpa [out,start] using (searchBank_input start n).trans hr.2.2.2.2.2.2
  have hthree : start 3 = b 3 := by simp [start,readyBank,parsedBank,header,write]
  have hout3 : out 3 = b 3 := by simpa [out,hthree] using searchBank_three start n
  have hout5 : out 5 = Source284Parser.length (b 4) := by
    simpa [out,start,hr.1] using searchBank_five start n
  have hscratch : out 9=0 ∧ out 10=0 ∧ out 11=0 := by
    simpa [out] using searchBank_scratch start n hs9 hs10 hs11
  have handoff : CandidateHandoff b out := ⟨hout,hout3,hout5,hscratch.1,hscratch.2.1,hscratch.2.2⟩
  have hz0 : start 0 = 0 := by simp [start,readyBank,parsedBank,header,write]
  have hout0 : out 0 = 0 := by simpa [out,hz0] using searchBank_zero start n
  refine ⟨k+searchCost start n,out,by omega,?_,?_,handoff,hout0⟩
  · rw [WordEventSystem.advance_add,hsetup]
    have h := hsearch.2.1
    change target.system.advance ⟨31,start⟩ (searchCost start n) = _ at h
    have hbool : Source284Relative.acceptBound (start 6) 0 (start 5) n =
        Source284Comparison.reference (b 4) := by
      simp [start,n,Source284Comparison.reference,hr.1,hr.2.1]
    rw [hbool] at h
    exact h
  · rw [WordEventSystem.wordFrom_add,hsetup,wsetup]
    have h := hsearch.2.2
    change target.system.wordFrom ⟨31,start⟩ (searchCost start n) = [] at h
    rw [h]; rfl

/-- The supplied-bank reference execution is a finite trace of the graph
parsed from the embedded source grammar. -/
theorem embedded_reference_from_pc2 (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
        (fun g => Grammar284.coreGraph g 53)).bind
        (fun g => GraphExtendedTrace.graphTrace g ⟨2,b⟩ time) =
      some (⟨if Source284Comparison.reference (b 4) then 87 else 89,out⟩,[]) ∧
      CandidateHandoff b out ∧ out 0 = 0 := by
  obtain ⟨time,out,ht,ha,hw,hi,hz⟩ := reference_from_pc2 b h9 h10 h11
  refine ⟨time,out,ht,?_,hi,hz⟩
  rw [Grammar284CoreTrace.embeddedGraph_run,ha,hw]

theorem row87_zero (b : Bank) (h : b 0=0) :
    target.system.step ⟨87,b⟩ = (⟨88,b⟩,[]) := by
  have hw : write b 0 0 = b := by
    funext i
    by_cases hi : i=0
    · subst i; simp [write,h]
    · simp [write,hi]
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,h,hw]

theorem row88 (b : Bank) :
    target.system.step ⟨88,b⟩ = (⟨89,write b 0 (b 0+1)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix]

/-- The complete reference phase reaches the actual common candidate-phase
entry PC 89. Register 0 holds precisely the source reference bit, and the
original input remains intact. -/
theorem reference_ready_from_pc2 (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      target.system.advance ⟨2,b⟩ time = ⟨89,out⟩ ∧
      target.system.wordFrom ⟨2,b⟩ time = [] ∧ CandidateHandoff b out ∧
      out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) := by
  obtain ⟨time,out,ht,ha,hw,hi,hz⟩ := reference_from_pc2 b h9 h10 h11
  by_cases href : Source284Comparison.reference (b 4) = true
  · have hstate : target.system.advance ⟨2,b⟩ time = ⟨87,out⟩ := by simpa [href] using ha
    have hfinish : target.system.advance ⟨87,out⟩ 2 = ⟨89,write out 0 1⟩ ∧
        target.system.wordFrom ⟨87,out⟩ 2 = [] := by
      simp [WordEventSystem.advance,WordEventSystem.wordFrom,row87_zero out hz,row88,hz]
    refine ⟨time+2,write out 0 1,by omega,?_,?_,?_,?_⟩
    · rw [WordEventSystem.advance_add,hstate,hfinish.1]
    · rw [WordEventSystem.wordFrom_add,hstate,hw,hfinish.2]; rfl
    · simpa [CandidateHandoff,write] using hi
    · simp [write,href]
  · have href0 : Source284Comparison.reference (b 4) = false := by
      cases h : Source284Comparison.reference (b 4) <;> simp_all
    refine ⟨time,out,ht,?_,hw,hi,?_⟩
    · simpa [href0] using ha
    · simpa [href0] using hz

/-- The parsed producer graph reaches the same candidate-phase entry with
the exact reference bit and no emitted events. -/
theorem embedded_reference_ready (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
        (fun g => Grammar284.coreGraph g 53)).bind
        (fun g => GraphExtendedTrace.graphTrace g ⟨2,b⟩ time) = some (⟨89,out⟩,[]) ∧
      CandidateHandoff b out ∧ out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) := by
  obtain ⟨time,out,ht,ha,hw,hi,hbit⟩ := reference_ready_from_pc2 b h9 h10 h11
  refine ⟨time,out,ht,?_,hi,hbit⟩
  rw [Grammar284CoreTrace.embeddedGraph_run,ha,hw]

end Shared.Beeping.NPcoNP.Source284GraphReferenceComplete
