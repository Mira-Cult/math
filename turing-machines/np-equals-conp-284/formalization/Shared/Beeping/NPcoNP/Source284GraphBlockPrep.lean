import Shared.Beeping.NPcoNP.Source284GraphBlockLookup
import Shared.Beeping.NPcoNP.Source284GraphPrepStep

/-! Block-residence certificates for source-step preparation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphBlockPrep
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphBlockSafety
open Shared.Beeping.NPcoNP.Source284GraphApplyRow (regs)
open Shared.Beeping.NPcoNP.Source284GraphRowStep (regs_eq_bank)
open Shared.Beeping.NPcoNP.Source284GraphPrepStep
open Shared.Beeping.NPcoNP.Source284GraphFirstIteration (bank row54_positive row54_zero row55 row56 row57_positive row57_zero row58 row59_zero)
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem head (b : Bank) (l r s d t : Nat) :
    SafeSeg ⟨50,regs b l r (s+1) d 0 0 (t+1)⟩
      ⟨54,regs b l (r/2) (s+r%2) d 0 0 t⟩ (3+r%2) := by
  have h₁ := one _ _ (row50 b l r (s+1) d 0 0 t) (by simp [Inside])
  have h₂ := one _ _ (row51 b l r s d 0 0 t) (by simp [Inside])
  have h₃ := one _ _ (row52 b l r s d 0 0 t) (by simp [Inside])
  by_cases h : r%2=1
  · have h₃' : SafeSeg ⟨52,regs b l r s d 0 0 t⟩ ⟨53,regs b l (r/2) s d 0 0 t⟩ 1 := by
      simpa [h] using h₃
    have h₄ := one _ _ (row53 b l (r/2) s d 0 0 t) (by simp [Inside])
    simpa [h] using cat (cat (cat h₁ h₂) h₃') h₄
  · have hz : r%2=0 := by omega
    have h₃' : SafeSeg ⟨52,regs b l r s d 0 0 t⟩ ⟨54,regs b l (r/2) s d 0 0 t⟩ 1 := by
      simpa [hz] using h₃
    simpa [hz] using cat (cat h₁ h₂) h₃'

theorem drain (b : Bank) (s x y z t : Nat) :
    SafeSeg ⟨54,bank b s x y z t⟩ ⟨57,bank b s 0 (y+x) (z+x) t⟩ (3*x+1) := by
  induction x generalizing y z with
  | zero => simpa using one _ _ (row54_zero b s y z t) (by simp [Inside])
  | succ x ih =>
    have h₁ := one _ _ (row54_positive b s x y z t) (by simp [Inside])
    have h₂ := one _ _ (row55 b s x y z t) (by simp [Inside])
    have h₃ := one _ _ (row56 b s x y (z+1) t) (by simp [Inside])
    have h₄ := ih (y+1) (z+1)
    have ht : ((1+1)+1)+(3*x+1)=3*(x+1)+1 := by omega
    have hy : y+1+x=y+(x+1) := by omega
    have hz : z+1+x=z+(x+1) := by omega
    simpa only [ht,hy,hz] using cat (cat (cat h₁ h₂) h₃) h₄

theorem restore (b : Bank) (s x y z t : Nat) :
    SafeSeg ⟨57,bank b s x y z t⟩ ⟨59,bank b s (x+y) 0 z t⟩ (2*y+1) := by
  induction y generalizing x with
  | zero => simpa using one _ _ (row57_zero b s x z t) (by simp [Inside])
  | succ y ih =>
    have h₁ := one _ _ (row57_positive b s x y z t) (by simp [Inside])
    have h₂ := one _ _ (row58 b s x y z t) (by simp [Inside])
    have h₃ := ih (x+1)
    have ht : (1+1)+(2*y+1)=2*(y+1)+1 := by omega
    have hx : x+1+y=x+(y+1) := by omega
    simpa only [ht,hx] using cat (cat h₁ h₂) h₃

theorem copy_description (b : Bank) (l r s d t : Nat) :
    SafeSeg ⟨54,regs b l r s d 0 0 t⟩ ⟨60,regs b l r s d 0 d t⟩ (5*d+3) := by
  let base := write (write b 8 l) 1 r
  have h₁ : SafeSeg ⟨54,regs b l r s d 0 0 t⟩ ⟨57,regs b l r s 0 d d t⟩ (3*d+1) := by
    simpa only [regs_eq_bank,zero_add] using drain base s d 0 0 t
  have h₂ : SafeSeg ⟨57,regs b l r s 0 d d t⟩ ⟨59,regs b l r s d 0 d t⟩ (2*d+1) := by
    simpa only [regs_eq_bank,zero_add] using restore base s 0 d d t
  have h₃ : SafeSeg ⟨59,regs b l r s d 0 d t⟩ ⟨60,regs b l r s d 0 d t⟩ 1 := by
    have he := row59_zero base s d d t
    dsimp only [base] at he
    have he' : target.system.step ⟨59,regs b l r s d 0 d t⟩ =
        (⟨60,regs b l r s d 0 d t⟩,[]) := by simpa only [regs_eq_bank] using he
    exact one _ _ he' (by simp [Inside])
  have ht : (3*d+1)+(2*d+1)+1=5*d+3 := by omega
  simpa only [ht] using cat (cat h₁ h₂) h₃

theorem prepare (b : Bank) (l r s d t : Nat) :
    SafeSeg ⟨50,regs b l r (s+1) d 0 0 (t+1)⟩
      ⟨60,regs b l (r/2) (s+r%2) d 0 d t⟩ (prepareCost d r) :=
  cat (head b l r s d t) (copy_description b l (r/2) (s+r%2) d t)

end Shared.Beeping.NPcoNP.Source284GraphBlockPrep
