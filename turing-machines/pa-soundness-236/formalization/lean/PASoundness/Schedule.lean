import PASoundness.Cantor
import PASoundness.Observer

/-! Exact repeated-address schedule of the pinned PA source. -/
namespace PASoundness.Schedule
open PASoundness.Cantor

/-- Prefix coordinate extraction has structural finite recursion. -/
def decodeCoordinates : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, z => (unpair z).1 :: decodeCoordinates n (unpair z).2

def packCoordinates : List Nat → Nat → Nat
  | [], tail => tail
  | x::xs, tail => pair x (packCoordinates xs tail)

@[simp] theorem decodeCoordinates_length (n z : Nat) :
    (decodeCoordinates n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [decodeCoordinates, ih]

@[simp] theorem decode_pack (xs : List Nat) (tail : Nat) :
    decodeCoordinates xs.length (packCoordinates xs tail) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [decodeCoordinates, packCoordinates, ih]

theorem tail_le_pack (xs : List Nat) (tail : Nat) :
    tail ≤ packCoordinates xs tail := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans ih (right_le_pair _ _)

def scheduledAddress (stage : Nat) : Observer.Address :=
  let nr := unpair stage
  let pr := unpair nr.2
  ⟨nr.1+1, pr.1, decodeCoordinates (nr.1+1) pr.2⟩

def stageForAddress (a : Observer.Address) (tail : Nat) : Nat :=
  pair (a.rank-1) (pair a.certificate (packCoordinates a.coordinates tail))

theorem scheduled_admissible (stage : Nat) :
    Observer.Admissible .legacy (scheduledAddress stage) := by
  simp [Observer.Admissible, scheduledAddress]

/-- Exact address recovery; the residual tail is deliberately ignored. -/
theorem scheduled_stageForAddress (a : Observer.Address)
    (ha : Observer.Admissible .legacy a) (tail : Nat) :
    scheduledAddress (stageForAddress a tail) = a := by
  have hr : 0 < a.rank := ha.2 rfl
  have hlen := ha.1
  have hrank : a.rank-1+1 = a.rank := by omega
  simp only [scheduledAddress, stageForAddress, unpair_pair, hrank]
  rw [← hlen, decode_pack]
  cases a
  simp_all

theorem tail_le_stage (a : Observer.Address) (tail : Nat) :
    tail ≤ stageForAddress a tail :=
  Nat.le_trans (tail_le_pack a.coordinates tail)
    (Nat.le_trans (right_le_pair _ _) (right_le_pair _ _))

/-- Every admissible finite key occurs past every bound, hence at a finite
stage and repeatedly. This fixes the actual key order, not just some fair order. -/
theorem schedule_fair (a : Observer.Address) (ha : Observer.Admissible .legacy a)
    (bound : Nat) : ∃ stage, bound < stage ∧ scheduledAddress stage = a := by
  refine ⟨stageForAddress a (bound+1), ?_, scheduled_stageForAddress a ha _⟩
  have h := tail_le_stage a (bound+1)
  omega

example : scheduledAddress 0 = ⟨1,0,[0]⟩ := by
  simp [scheduledAddress, unpair, unpairAux, decodeCoordinates]
example : scheduledAddress 1 = ⟨2,0,[0,0]⟩ := by
  simp [scheduledAddress, unpair, unpairAux, decodeCoordinates]
example : unpair (pair 17 29) = (17,29) := unpair_pair 17 29

end PASoundness.Schedule
