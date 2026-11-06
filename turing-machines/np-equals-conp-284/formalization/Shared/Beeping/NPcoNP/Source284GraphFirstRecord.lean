import Shared.Beeping.NPcoNP.Source284GraphReferenceFirstStep
import Shared.Beeping.NPcoNP.Source284Relative
import Shared.Beeping.NPcoNP.Grammar284CoreTrace

/-! The first positive-clock reference attempt continues through lookup of
record zero in the checked coalesced register graph. This is not a physical
tape simulation or a proof of later interpreter iterations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284GraphFirstRecord

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphFirstIteration
open Shared.Beeping.NPcoNP.Source284GraphReferenceAttempt
open Shared.Beeping.NPcoNP.Source284Relative (readRecord readRecord_even readRecord_odd)

abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- Transfer the temporary copy of the description from register 10 to 9. -/
theorem row60_positive (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨60,bank b s x y (z+1) t⟩ =
      (⟨61,bank b s x y z t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write10]

theorem row60_zero (b : Bank) (s x y t : Nat) :
    target.system.step ⟨60,bank b s x y 0 t⟩ = (⟨62,bank b s x y 0 t⟩,[]) := by rfl

theorem row61 (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨61,bank b s x y z t⟩ = (⟨60,bank b s x (y+1) z t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write9]

theorem transfer (b : Bank) (s x y z t : Nat) :
    target.system.advance ⟨60,bank b s x y z t⟩ (2*z+1) =
      ⟨62,bank b s x (y+z) 0 t⟩ ∧
    target.system.wordFrom ⟨60,bank b s x y z t⟩ (2*z+1) = [] := by
  induction z generalizing y with
  | zero => simp [WordEventSystem.advance,WordEventSystem.wordFrom,row60_zero]
  | succ z ih =>
    have hs : target.system.advance ⟨60,bank b s x y (z+1) t⟩ 2 =
        ⟨60,bank b s x (y+1) z t⟩ ∧
        target.system.wordFrom ⟨60,bank b s x y (z+1) t⟩ 2 = [] := by
      simp [WordEventSystem.advance,WordEventSystem.wordFrom,row60_positive,row61]
    have ht : 2*(z+1)+1 = 2+(2*z+1) := by omega
    have hy : y+1+z = y+(z+1) := by omega
    constructor
    · rw [ht,WordEventSystem.advance_add,hs.1,(ih (y+1)).1,hy]
    · rw [ht,WordEventSystem.wordFrom_add,hs.1,hs.2,(ih (y+1)).2]; simp

theorem row62_zero (b : Bank) (x y z t : Nat) :
    target.system.step ⟨62,bank b 0 x y z t⟩ = (⟨64,bank b 0 x y z t⟩,[]) := by rfl

theorem row64_zero (b : Bank) (x y z t : Nat) :
    target.system.step ⟨64,bank b 0 x y z t⟩ = (⟨65,bank b 0 x y z t⟩,[]) := by rfl

theorem row65_odd (b : Bank) (s x y z t : Nat) (h : y%2=1) :
    target.system.step ⟨65,bank b s x y z t⟩ =
      (⟨66,bank b s x (y/2) z t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9,h]

theorem row65_even (b : Bank) (s x y z t : Nat) (h : y%2=0) :
    target.system.step ⟨65,bank b s x y z t⟩ =
      (⟨67,bank b s x (y/2) z t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9,h]

theorem row66 (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨66,bank b s x y z t⟩ = (⟨65,bank b (s+1) x y z t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2]

theorem row67_positive (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨67,bank b s x (y+1) z t⟩ = (⟨67,bank b s x y z t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9]

theorem row67_zero (b : Bank) (s x z t : Nat) :
    target.system.step ⟨67,bank b s x 0 z t⟩ = (⟨68,bank b s x 0 z t⟩,[]) := by rfl

/-- Decode the first unary record, leaving its unused high suffix for the
following explicit clearing loop. The number of odd marker bits is charged. -/
theorem decode (b : Bank) (s x digit z t : Nat) :
    let result := readRecord digit
    let cost := 2*result.1+1
    target.system.advance ⟨65,bank b s x digit z t⟩ cost =
      ⟨67,bank b (s+result.1) x result.2 z t⟩ ∧
    target.system.wordFrom ⟨65,bank b s x digit z t⟩ cost = [] := by
  induction digit using Nat.strong_induction_on generalizing s with
  | h digit ih =>
    by_cases ho : digit%2=1
    · have hp : 0 < digit := by omega
      have hd : digit/2 < digit := Nat.div_lt_self hp (by decide)
      have hs : target.system.advance ⟨65,bank b s x digit z t⟩ 2 =
          ⟨65,bank b (s+1) x (digit/2) z t⟩ ∧
          target.system.wordFrom ⟨65,bank b s x digit z t⟩ 2 = [] := by
        simp [WordEventSystem.advance,WordEventSystem.wordFrom,row65_odd b s x digit z t ho,row66]
      have hi := ih (digit/2) hd (s+1)
      rw [readRecord_odd digit ho]
      dsimp only
      dsimp only at hi
      have hc : 2*((readRecord (digit/2)).1+1)+1 = 2+(2*(readRecord (digit/2)).1+1) := by omega
      rw [hc]
      constructor
      · rw [WordEventSystem.advance_add,hs.1,hi.1]
        have heq : (s+1)+(readRecord (digit/2)).1 = s+((readRecord (digit/2)).1+1) := by omega
        rw [heq]
      · rw [WordEventSystem.wordFrom_add,hs.1,hs.2,hi.2]; simp
    · have he : digit%2=0 := by omega
      rw [readRecord_even digit he]
      simp [WordEventSystem.advance,WordEventSystem.wordFrom,row65_even b s x digit z t he]

/-- Clear the suffix without a hidden unbounded operation. -/
theorem clear_suffix (b : Bank) (s x y z t : Nat) :
    target.system.advance ⟨67,bank b s x y z t⟩ (y+1) = ⟨68,bank b s x 0 z t⟩ ∧
    target.system.wordFrom ⟨67,bank b s x y z t⟩ (y+1) = [] := by
  induction y with
  | zero => simp [WordEventSystem.advance,WordEventSystem.wordFrom,row67_zero]
  | succ y ih =>
    have hs : target.system.step ⟨67,bank b s x (y+1) z t⟩ =
        (⟨67,bank b s x y z t⟩,[]) := row67_positive b s x y z t
    have ht : y+1+1 = 1+(y+1) := by omega
    constructor
    · rw [ht,WordEventSystem.advance_add]
      simpa [WordEventSystem.advance,hs] using ih.1
    · rw [ht,WordEventSystem.wordFrom_add]
      simpa [WordEventSystem.advance,WordEventSystem.wordFrom,hs] using ih.2

/-- The exact charged graph-step cost of copying, decoding and clearing the
first unary record. -/
def lookupCost (x : Nat) : Nat :=
  (2*x+1)+2+(2*(readRecord x).1+1)+((readRecord x).2+1)

/-- From the first-iteration handoff at PC 60, the checked graph reaches
PC 68 with the exact first source record in register 2. It preserves the
source description in register 6, clears both scratch registers, and emits
no output. -/
theorem first_record (b : Bank) (x t : Nat) :
    0 < lookupCost x ∧
    target.system.advance ⟨60,bank b 0 x 0 x t⟩ (lookupCost x) =
      ⟨68,bank b (readRecord x).1 x 0 0 t⟩ ∧
    target.system.wordFrom ⟨60,bank b 0 x 0 x t⟩ (lookupCost x) = [] := by
  have ha := transfer b 0 x 0 x t
  have hcopy : target.system.advance ⟨60,bank b 0 x 0 x t⟩ (2*x+1) =
      ⟨62,bank b 0 x x 0 t⟩ := by simpa using ha.1
  have hcopyword : target.system.wordFrom ⟨60,bank b 0 x 0 x t⟩ (2*x+1) = [] := ha.2
  have htwo : target.system.advance ⟨62,bank b 0 x x 0 t⟩ 2 =
      ⟨65,bank b 0 x x 0 t⟩ ∧
      target.system.wordFrom ⟨62,bank b 0 x x 0 t⟩ 2 = [] := by
    simp [WordEventSystem.advance,WordEventSystem.wordFrom,row62_zero,row64_zero]
  have hd := decode b 0 x x 0 t
  dsimp only at hd
  have hc := clear_suffix b (readRecord x).1 x (readRecord x).2 0 t
  have h₁ : target.system.advance ⟨60,bank b 0 x 0 x t⟩ ((2*x+1)+2) =
      ⟨65,bank b 0 x x 0 t⟩ := by rw [WordEventSystem.advance_add,hcopy,htwo.1]
  have w₁ : target.system.wordFrom ⟨60,bank b 0 x 0 x t⟩ ((2*x+1)+2) = [] := by
    rw [WordEventSystem.wordFrom_add,hcopy,hcopyword,htwo.2]; rfl
  have h₂ : target.system.advance ⟨60,bank b 0 x 0 x t⟩
      (((2*x+1)+2)+(2*(readRecord x).1+1)) =
      ⟨67,bank b (readRecord x).1 x (readRecord x).2 0 t⟩ := by
    rw [WordEventSystem.advance_add,h₁]
    simpa using hd.1
  have w₂ : target.system.wordFrom ⟨60,bank b 0 x 0 x t⟩
      (((2*x+1)+2)+(2*(readRecord x).1+1)) = [] := by
    rw [WordEventSystem.wordFrom_add,h₁,w₁]
    simpa using hd.2
  refine ⟨by simp [lookupCost], ?_, ?_⟩
  · unfold lookupCost
    rw [WordEventSystem.advance_add,h₂,hc.1]
  · unfold lookupCost
    rw [WordEventSystem.wordFrom_add,h₂,w₂,hc.2]; rfl

/-- Compose reference-attempt setup, its first evaluator iteration, and the
complete record-zero lookup. Every graph step is finite and silent. -/
theorem reference_first_record (b : Bank) (h7 : 0 < b 7) (h5 : 0 < b 5)
    (h9 : b 9 = 0) (h10 : b 10 = 0) (h11 : b 11 = 0) :
    let r := ready b
    let d := ((7*(b 7-1)+b 8+5) + (b 1+b 2+7*b 5+6)) + (5*b 6+6)
    0 < d+lookupCost (b 6) ∧
      target.system.advance ⟨31,b⟩ (d+lookupCost (b 6)) =
        ⟨68,bank r (readRecord (b 6)).1 (b 6) 0 0 (b 5-1)⟩ ∧
      target.system.wordFrom ⟨31,b⟩ (d+lookupCost (b 6)) = [] := by
  have h₁ := Source284GraphReferenceFirstStep.reference_first_step b h7 h5 h9 h10 h11
  have h₂ := first_record (ready b) (b 6) (b 5-1)
  dsimp only at h₁ ⊢
  refine ⟨by omega, ?_, ?_⟩
  · rw [WordEventSystem.advance_add,h₁.2.1,h₂.2.1]
  · rw [WordEventSystem.wordFrom_add,h₁.2.1,h₁.2.2,h₂.2.2]; rfl

/-- The next graph transition splits the decoded row into its write-bit
branch and the remaining row quotient. -/
theorem row68 (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨68,bank b s x y z t⟩ =
      (⟨if s%2=1 then 69 else 70,bank b (s/2) x y z t⟩,[]) := by
  by_cases h : s%2=1
  · simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2,h]
  · have hz : s%2=0 := by omega
    simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2,h,hz]

/-- The first source row is decoded, including its write-bit branch, after
one additional charged graph step. Both possible branches remain silent. -/
theorem first_record_write_branch (b : Bank) (x t : Nat) :
    target.system.advance ⟨60,bank b 0 x 0 x t⟩ (lookupCost x+1) =
      ⟨if (readRecord x).1%2=1 then 69 else 70,
        bank b ((readRecord x).1/2) x 0 0 t⟩ ∧
    target.system.wordFrom ⟨60,bank b 0 x 0 x t⟩ (lookupCost x+1) = [] := by
  have h := first_record b x t
  constructor
  · rw [WordEventSystem.advance_add,h.2.1]
    simpa [WordEventSystem.advance] using congrArg Prod.fst (row68 b (readRecord x).1 x 0 0 t)
  · rw [WordEventSystem.wordFrom_add,h.2.1,h.2.2]
    simp [WordEventSystem.wordFrom,WordEventSystem.advance,row68]

/-- The same finite result holds for the graph parsed from the embedded
producer grammar, without assuming a graph-to-register correspondence. -/
theorem embedded_first_record (b : Bank) (x t : Nat) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g ⟨60,bank b 0 x 0 x t⟩ (lookupCost x)) =
    some (⟨68,bank b (readRecord x).1 x 0 0 t⟩,[]) := by
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := first_record b x t
  rw [h.2.1,h.2.2]

/-- The parsed producer graph also performs the complete PC-31 setup and
first-record lookup, with its exact silent word and stated preconditions. -/
theorem embedded_reference_first_record (b : Bank) (h7 : 0 < b 7) (h5 : 0 < b 5)
    (h9 : b 9 = 0) (h10 : b 10 = 0) (h11 : b 11 = 0) :
    let r := ready b
    let d := ((7*(b 7-1)+b 8+5) + (b 1+b 2+7*b 5+6)) + (5*b 6+6)
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g ⟨31,b⟩ (d+lookupCost (b 6))) =
    some (⟨68,bank r (readRecord (b 6)).1 (b 6) 0 0 (b 5-1)⟩,[]) := by
  dsimp only
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := reference_first_record b h7 h5 h9 h10 h11
  dsimp only at h
  rw [h.2.1,h.2.2]

end Shared.Beeping.NPcoNP.Source284GraphFirstRecord
