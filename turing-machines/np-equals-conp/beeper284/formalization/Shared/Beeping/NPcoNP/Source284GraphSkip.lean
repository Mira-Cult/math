import Shared.Beeping.NPcoNP.Source284GraphFirstRecord

/-! Generic record skipping in the checked coalesced graph. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284GraphSkip
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphFirstIteration
open Shared.Beeping.NPcoNP.Source284GraphFirstRecord
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem row62_positive (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨62,bank b (s+1) x y z t⟩ = (⟨63,bank b s x y z t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2]

theorem row63_odd (b : Bank) (s x y z t : Nat) (h : y%2=1) :
    target.system.step ⟨63,bank b s x y z t⟩ = (⟨63,bank b s x (y/2) z t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9,h]

theorem row63_even (b : Bank) (s x y z t : Nat) (h : y%2=0) :
    target.system.step ⟨63,bank b s x y z t⟩ = (⟨62,bank b s x (y/2) z t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9,h]

/-- Skip one complete unary record, including its terminating zero. -/
theorem skip_one (b : Bank) (s x digit z t : Nat) :
    target.system.advance ⟨63,bank b s x digit z t⟩ ((readRecord digit).1+1) =
      ⟨62,bank b s x (readRecord digit).2 z t⟩ ∧
    target.system.wordFrom ⟨63,bank b s x digit z t⟩ ((readRecord digit).1+1) = [] := by
  induction digit using Nat.strong_induction_on with
  | h digit ih =>
    by_cases ho : digit%2=1
    · have hd : digit/2 < digit := Nat.div_lt_self (by omega) (by decide)
      have hrow := row63_odd b s x digit z t ho
      have hi := ih (digit/2) hd
      rw [readRecord_odd digit ho]
      dsimp only
      have hc : (readRecord (digit/2)).1+1+1 = 1+((readRecord (digit/2)).1+1) := by omega
      rw [hc]
      constructor
      · rw [WordEventSystem.advance_add]
        simpa [WordEventSystem.advance,hrow] using hi.1
      · rw [WordEventSystem.wordFrom_add]
        simpa [WordEventSystem.advance,WordEventSystem.wordFrom,hrow] using hi.2
    · have he : digit%2=0 := by omega
      rw [readRecord_even digit he]
      simp [WordEventSystem.advance,WordEventSystem.wordFrom,row63_even b s x digit z t he]

def skipCost (digit : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => 1+((readRecord digit).1+1)+skipCost (readRecord digit).2 n

/-- Skip every preceding record; every marker and every control step is
charged. The loop accepts arbitrary input digits, including virtual zeros. -/
theorem skip (b : Bank) (n x digit z t : Nat) :
    target.system.advance ⟨62,bank b n x digit z t⟩ (skipCost digit n) =
      ⟨64,bank b 0 x (dropRecords digit n) z t⟩ ∧
    target.system.wordFrom ⟨62,bank b n x digit z t⟩ (skipCost digit n) = [] := by
  induction n generalizing digit with
  | zero => simp [skipCost,dropRecords,WordEventSystem.advance,WordEventSystem.wordFrom,row62_zero]
  | succ n ih =>
    have hs := row62_positive b n x digit z t
    have ho := skip_one b n x digit z t
    have hi := ih (readRecord digit).2
    simp only [skipCost,dropRecords]
    have h₁ : target.system.advance ⟨62,bank b (n+1) x digit z t⟩ 1 =
        ⟨63,bank b n x digit z t⟩ := by simpa [WordEventSystem.advance] using congrArg Prod.fst hs
    have w₁ : target.system.wordFrom ⟨62,bank b (n+1) x digit z t⟩ 1 = [] := by
      simpa [WordEventSystem.wordFrom,WordEventSystem.advance] using congrArg Prod.snd hs
    constructor
    · rw [WordEventSystem.advance_add,WordEventSystem.advance_add,h₁,ho.1,hi.1]
    · rw [WordEventSystem.wordFrom_add,WordEventSystem.advance_add,h₁,ho.1,hi.2]
      rw [WordEventSystem.wordFrom_add,h₁,w₁,ho.2]; rfl

/-- Exact graph steps for transferring the source description, skipping
preceding records, decoding the selected record, and clearing its suffix. -/
def lookupCost (description ordinal : Nat) : Nat :=
  let out := readRecord (dropRecords description ordinal)
  (2*description+1)+skipCost description ordinal+1+(2*out.1+1)+(out.2+1)

/-- Lookup of every natural-number source record, with explicit finite cost
and no output. The ordinal is held in register 2 at entry. -/
theorem lookup (b : Bank) (ordinal description clock : Nat) :
    let r := readRecord (dropRecords description ordinal)
    0 < lookupCost description ordinal ∧
    target.system.advance ⟨60,bank b ordinal description 0 description clock⟩
      (lookupCost description ordinal) =
        ⟨68,bank b r.1 description 0 0 clock⟩ ∧
    target.system.wordFrom ⟨60,bank b ordinal description 0 description clock⟩
      (lookupCost description ordinal) = [] := by
  let a := 2*description+1
  let k := skipCost description ordinal
  let rem := dropRecords description ordinal
  let r := readRecord rem
  let c := 2*r.1+1
  let f := r.2+1
  let initial := (⟨60,bank b ordinal description 0 description clock⟩ :
    PASoundness.RegisterMachine.Config 12 185)
  have ht := transfer b ordinal description 0 description clock
  have hcopy : target.system.advance initial a = ⟨62,bank b ordinal description description 0 clock⟩ := by
    simpa [initial,a] using ht.1
  have wcopy : target.system.wordFrom initial a = [] := by simpa [initial,a] using ht.2
  have hs := skip b ordinal description description 0 clock
  have hskip : target.system.advance ⟨62,bank b ordinal description description 0 clock⟩ k =
      ⟨64,bank b 0 description rem 0 clock⟩ := by simpa [k,rem] using hs.1
  have wskip : target.system.wordFrom ⟨62,bank b ordinal description description 0 clock⟩ k = [] := by
    simpa [k] using hs.2
  have h₁ : target.system.advance initial (a+k) = ⟨64,bank b 0 description rem 0 clock⟩ := by
    rw [WordEventSystem.advance_add,hcopy,hskip]
  have w₁ : target.system.wordFrom initial (a+k) = [] := by
    rw [WordEventSystem.wordFrom_add,hcopy,wcopy,wskip]; rfl
  have h₂ : target.system.advance initial (a+k+1) = ⟨65,bank b 0 description rem 0 clock⟩ := by
    rw [WordEventSystem.advance_add,h₁]
    simp [WordEventSystem.advance,row64_zero]
  have w₂ : target.system.wordFrom initial (a+k+1) = [] := by
    rw [WordEventSystem.wordFrom_add,h₁,w₁]
    simp [WordEventSystem.wordFrom,WordEventSystem.advance,row64_zero]
  have hd := decode b 0 description rem 0 clock
  dsimp only at hd
  have h₃ : target.system.advance initial (a+k+1+c) =
      ⟨67,bank b r.1 description r.2 0 clock⟩ := by
    rw [WordEventSystem.advance_add,h₂]
    simpa [c,r] using hd.1
  have w₃ : target.system.wordFrom initial (a+k+1+c) = [] := by
    rw [WordEventSystem.wordFrom_add,h₂,w₂]
    simpa [c,r] using hd.2
  have hf := clear_suffix b r.1 description r.2 0 clock
  have hcost : lookupCost description ordinal = a+k+1+c+f := by rfl
  refine ⟨?_,?_,?_⟩
  · rw [hcost]; dsimp [a]; omega
  · change target.system.advance initial (lookupCost description ordinal) = _
    rw [hcost,WordEventSystem.advance_add,h₃]
    simpa [f,r,rem] using hf.1
  · change target.system.wordFrom initial (lookupCost description ordinal) = []
    rw [hcost,WordEventSystem.wordFrom_add,h₃,w₃]
    simpa [f] using hf.2

/-- The same theorem uses the exact numeric source evaluator's `record`
function, rather than a separately postulated decoder. -/
theorem lookup_record (b : Bank) (ordinal description clock : Nat) :
    target.system.advance ⟨60,bank b ordinal description 0 description clock⟩
      (lookupCost description ordinal) =
        ⟨68,bank b (record description ordinal) description 0 0 clock⟩ ∧
    target.system.wordFrom ⟨60,bank b ordinal description 0 description clock⟩
      (lookupCost description ordinal) = [] := by
  simpa [record] using (lookup b ordinal description clock).2

/-- The bound graph is extracted from the pinned embedded grammar. -/
theorem embedded_lookup (b : Bank) (ordinal description clock : Nat) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g
        ⟨60,bank b ordinal description 0 description clock⟩ (lookupCost description ordinal)) =
    some (⟨68,bank b (record description ordinal) description 0 0 clock⟩,[]) := by
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := lookup_record b ordinal description clock
  rw [h.1,h.2]

end Shared.Beeping.NPcoNP.Source284GraphSkip
