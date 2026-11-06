import Shared.Beeping.NPcoNP.Source284GraphApplyLoops

/-! Compose the checked row-decoding, swap, and write loops into one finite
silent source-row action on the checked register graph. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphApplyCorrect

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops

abbrev Bank := PASoundness.RegisterMachine.Bank 12

def swapCost (l r : Nat) : Nat := (2*l+1)+(2*r+1)+(2*l+1)

def writeCost (l bit : Nat) : Nat := (3*l+1)+(2*bit+1)+1+(2*(2*l+bit)+1)

/-- The direction-change branch swaps the complete two source halves. -/
theorem swap (b : Bank) (l r s d a t : Nat) :
    Seg ⟨71,regs b l r s d a 0 t⟩ ⟨77,regs b r l s d a 0 t⟩ (swapCost l r) := by
  have h₁ := swap_left b l r s d a 0 t
  have h₂ := swap_right b 0 r s d a l t
  have h₃ := swap_restore b r 0 s d a l t
  have h₁₂ := cat h₁ (by simpa using h₂)
  have h := cat h₁₂ (by simpa using h₃)
  simpa [swapCost] using h

/-- The write path doubles the selected half and appends the decoded bit.
Both scratch registers are cleared on return to PC 50. -/
theorem write_half (b : Bank) (l r s d bit t : Nat) :
    Seg ⟨77,regs b l r s d bit 0 t⟩
      ⟨50,regs b (2*l+bit) r s d 0 0 t⟩ (writeCost l bit) := by
  have h₁ := double_left b l r s d bit 0 t
  have h₂ := add_write b 0 r s d bit (2*l) t
  have h₃ : Seg ⟨82,regs b 0 r s d 0 (2*l+bit) t⟩
      ⟨83,regs b 0 r s d 0 (2*l+bit) t⟩ 1 := by
    simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row82_zero]
  have h₄ := write_back b 0 r s d 0 (2*l+bit) t
  have h₁₂ := cat h₁ (by simpa using h₂)
  have h₁₂₃ := cat h₁₂ h₃
  have h := cat h₁₂₃ h₄
  simpa [writeCost] using h

def applyCost (row l r : Nat) : Nat :=
  decodeCost row +
    if (row/2)%2=1 then swapCost l r + writeCost r (row%2)
    else writeCost l (row%2)

def leftAfter (row l r : Nat) : Nat :=
  if (row/2)%2=1 then 2*r+row%2 else 2*l+row%2

def rightAfter (row l r : Nat) : Nat :=
  if (row/2)%2=1 then l else r

/-- Every decoded row completes in a positive finite silent segment. The two
half-tape numerals and the state quotient are exactly the values used by the
numeric source-step semantics. -/
theorem apply (b : Bank) (l r row d t : Nat) :
    0 < applyCost row l r ∧
    Seg ⟨68,regs b l r row d 0 0 t⟩
      ⟨50,regs b (leftAfter row l r) (rightAfter row l r) (row/4) d 0 0 t⟩
      (applyCost row l r) := by
  have hd := decode_flags b l r row d t
  have hp : 0 < decodeCost row := by simp [decodeCost]
  constructor
  · unfold applyCost
    split <;> omega
  · by_cases h : (row/2)%2=1
    · have hd' : Seg ⟨68,regs b l r row d 0 0 t⟩
          ⟨71,regs b l r (row/4) d (row%2) 0 t⟩ (decodeCost row) := by
        simpa [Seg,h] using hd
      have hs := swap b l r (row/4) d (row%2) t
      have hw := write_half b r l (row/4) d (row%2) t
      have hseg := cat hd' (cat hs hw)
      simpa [applyCost,leftAfter,rightAfter,h] using hseg
    · have hd' : Seg ⟨68,regs b l r row d 0 0 t⟩
          ⟨77,regs b l r (row/4) d (row%2) 0 t⟩ (decodeCost row) := by
        simpa [Seg,h] using hd
      have hw := write_half b l r (row/4) d (row%2) t
      have hseg := cat hd' hw
      simpa [applyCost,leftAfter,rightAfter,h] using hseg

end Shared.Beeping.NPcoNP.Source284GraphApplyCorrect
