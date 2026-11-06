import Shared.Beeping.NPcoNP.Source284GraphCandidateMirror

/-! Composable safety for finite graph segments inside the checked evaluator
block. This is an intermediate invariant, not a physical-machine theorem. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphBlockSafety
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg)
abbrev Cfg := PASoundness.RegisterMachine.Config 12 185

def Inside (c : Cfg) : Prop := 50 ≤ c.state.val ∧ c.state.val < 85

def Safe (c : Cfg) (n : Nat) : Prop := ∀ t < n, Inside (target.system.advance c t)

def SafeSeg (a b : Cfg) (n : Nat) : Prop := Seg a b n ∧ Safe a n

theorem one (a b : Cfg) (h : target.system.step a = (b,[])) (ha : Inside a) : SafeSeg a b 1 := by
  constructor
  · simpa [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,h]
  · intro t ht
    have ht0 : t=0 := by omega
    subst t
    simpa [WordEventSystem.advance] using ha

theorem cat {a b c : Cfg} {n m : Nat} (h₁ : SafeSeg a b n) (h₂ : SafeSeg b c m) :
    SafeSeg a c (n+m) := by
  constructor
  · exact Source284GraphApplyLoops.cat h₁.1 h₂.1
  · intro t ht
    by_cases hn : t<n
    · exact h₁.2 t hn
    · let u := t-n
      have hsum : t=n+u := by dsimp [u]; omega
      have hu : u<m := by dsimp [u]; omega
      rw [hsum,WordEventSystem.advance_add,h₁.1.1]
      exact h₂.2 u hu

/-- A zero-length segment imposes no residence condition. -/
theorem zero (a : Cfg) : SafeSeg a a 0 := by
  simp [SafeSeg,Seg,Safe,WordEventSystem.advance,WordEventSystem.wordFrom]

end Shared.Beeping.NPcoNP.Source284GraphBlockSafety
