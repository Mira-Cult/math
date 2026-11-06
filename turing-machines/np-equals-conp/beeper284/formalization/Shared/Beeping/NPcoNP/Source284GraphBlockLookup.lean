import Shared.Beeping.NPcoNP.Source284GraphBlockSafety

/-! Block-residence certificates for every step of the numeric record lookup. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphBlockLookup
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphFirstIteration (bank)
open Shared.Beeping.NPcoNP.Source284GraphFirstRecord
open Shared.Beeping.NPcoNP.Source284GraphSkip (skipCost lookupCost)
open Shared.Beeping.NPcoNP.Source284GraphBlockSafety
open Shared.Beeping.NPcoNP.Source284Relative (readRecord readRecord_odd readRecord_even dropRecords record)
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem transfer (b : Bank) (s x y z t : Nat) :
    SafeSeg ⟨60,bank b s x y z t⟩ ⟨62,bank b s x (y+z) 0 t⟩ (2*z+1) := by
  induction z generalizing y with
  | zero =>
    simpa using one _ _ (row60_zero b s x y t) (by simp [Inside])
  | succ z ih =>
    have h₁ := one _ _ (row60_positive b s x y z t) (by simp [Inside])
    have h₂ := one _ _ (row61 b s x y z t) (by simp [Inside])
    have h := cat (cat h₁ h₂) (ih (y+1))
    have hy : y+1+z=y+(z+1) := by omega
    have ht : (1+1)+(2*z+1)=2*(z+1)+1 := by omega
    simpa only [hy,ht] using h

theorem skip_one (b : Bank) (s x digit z t : Nat) :
    SafeSeg ⟨63,bank b s x digit z t⟩ ⟨62,bank b s x (readRecord digit).2 z t⟩
      ((readRecord digit).1+1) := by
  induction digit using Nat.strong_induction_on with
  | h digit ih =>
    by_cases ho : digit%2=1
    · have hd : digit/2<digit := Nat.div_lt_self (by omega) (by simp [Inside])
      have h₁ := one _ _ (Source284GraphSkip.row63_odd b s x digit z t ho) (by simp [Inside])
      have h₂ := ih (digit/2) hd
      rw [readRecord_odd digit ho]
      dsimp only
      have hc : (readRecord (digit/2)).1+1+1=1+((readRecord (digit/2)).1+1) := by omega
      rw [hc]
      exact cat h₁ h₂
    · have he : digit%2=0 := by omega
      rw [readRecord_even digit he]
      simpa using one _ _ (Source284GraphSkip.row63_even b s x digit z t he) (by simp [Inside])

theorem skip (b : Bank) (n x digit z t : Nat) :
    SafeSeg ⟨62,bank b n x digit z t⟩ ⟨64,bank b 0 x (dropRecords digit n) z t⟩
      (skipCost digit n) := by
  induction n generalizing digit with
  | zero =>
    simpa [skipCost,dropRecords] using one _ _ (row62_zero b x digit z t) (by simp [Inside])
  | succ n ih =>
    have h₁ := one _ _ (Source284GraphSkip.row62_positive b n x digit z t) (by simp [Inside])
    have h₂ := skip_one b n x digit z t
    have h₃ := ih (readRecord digit).2
    simpa only [skipCost,dropRecords] using cat (cat h₁ h₂) h₃

theorem decode (b : Bank) (s x digit z t : Nat) :
    SafeSeg ⟨65,bank b s x digit z t⟩
      ⟨67,bank b (s+(readRecord digit).1) x (readRecord digit).2 z t⟩
      (2*(readRecord digit).1+1) := by
  induction digit using Nat.strong_induction_on generalizing s with
  | h digit ih =>
    by_cases ho : digit%2=1
    · have hd : digit/2<digit := Nat.div_lt_self (by omega) (by simp [Inside])
      have h₁ := one _ _ (row65_odd b s x digit z t ho) (by simp [Inside])
      have h₂ := one _ _ (row66 b s x (digit/2) z t) (by simp [Inside])
      have h₃ := ih (digit/2) hd (s+1)
      rw [readRecord_odd digit ho]
      dsimp only
      have hc : (1+1)+(2*(readRecord (digit/2)).1+1)=
          2*((readRecord (digit/2)).1+1)+1 := by omega
      have hs : (s+1)+(readRecord (digit/2)).1=s+((readRecord (digit/2)).1+1) := by omega
      simpa only [hc,hs] using cat (cat h₁ h₂) h₃
    · have he : digit%2=0 := by omega
      rw [readRecord_even digit he]
      simpa using one _ _ (row65_even b s x digit z t he) (by simp [Inside])

theorem clear_suffix (b : Bank) (s x y z t : Nat) :
    SafeSeg ⟨67,bank b s x y z t⟩ ⟨68,bank b s x 0 z t⟩ (y+1) := by
  induction y with
  | zero => simpa using one _ _ (row67_zero b s x z t) (by simp [Inside])
  | succ y ih =>
    have h₁ := one _ _ (row67_positive b s x y z t) (by simp [Inside])
    have ht : 1+(y+1)=y+1+1 := by omega
    simpa only [ht] using cat h₁ ih

/-- The complete record lookup remains in PCs 60 through 67 until its
PC-68 handoff, including virtual zero records. -/
theorem lookup (b : Bank) (ordinal description clock : Nat) :
    SafeSeg ⟨60,bank b ordinal description 0 description clock⟩
      ⟨68,bank b (record description ordinal) description 0 0 clock⟩
      (lookupCost description ordinal) := by
  let r := readRecord (dropRecords description ordinal)
  have h₁ := transfer b ordinal description 0 description clock
  have h₂ := skip b ordinal description description 0 clock
  have h₃ := one _ _ (row64_zero b description (dropRecords description ordinal) 0 clock) (by simp [Inside])
  have h₄ := decode b 0 description (dropRecords description ordinal) 0 clock
  have h₅ := clear_suffix b r.1 description r.2 0 clock
  have h := cat (cat (cat (cat (by simpa using h₁) h₂) h₃) (by simpa using h₄)) h₅
  simpa [Source284GraphSkip.lookupCost,r,record] using h

end Shared.Beeping.NPcoNP.Source284GraphBlockLookup
