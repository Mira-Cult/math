import Shared.PNP.Record285.HalfEvenPositive

/-! A common root-to-root contract for every native-half operand. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfComplete
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.Grammar

def evenConfig (code : List Bool) (gap : Nat) (bank : Nat) (head : Int) (leftTail : Nat) :
    PhysicalNumeric.Config 285 :=
  let p := peel code.reverse
  let q := peel p.2
  let precode := q.2.reverse
  let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
  SymbolicDispatch.denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
    (head-p.1-q.1-2) leftTail rightTail

def oddConfig (code : List Bool) (gap : Nat) (bank : Nat) (head : Int) (leftTail : Nat) :
    PhysicalNumeric.Config 285 :=
  let p := peel code.reverse
  let precode := p.2.reverse
  let rightTail := runPattern false (p.1+gap+1) true (2*bank)
  SymbolicDispatch.denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
    (head-p.1-1) leftTail rightTail

def evenControl (code : List Bool) : Prop :=
  returnPathSkipOne code = some ((peel (peel code.reverse).2).2.reverse++[true])

def oddControl (code : List Bool) : Prop :=
  returnPath code = some ((peel code.reverse).2.reverse++[true])

/-- Exact branch-specific full physical configuration after a half action.
For positive even inputs the common reserve includes one extra blank, which
is retained explicitly as part of the high suffix. -/
def Result (code : List Bool) (gap target : Nat) (before fields : List Nat)
    (head : Int) (leftTail retained : Nat) (out : Shared.Beeping.Machines.Config 285) : Prop :=
  (target = 0 ∧ evenControl code ∧
    Rel (evenConfig code gap (IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained))
      head leftTail) out) ∨
  (target = 1 ∧ oddControl code ∧
    Rel (oddConfig code gap (IncrementSelector.blocksBits (before++[0]++fields++[0]) retained)
      head leftTail) out) ∨
  (∃ n, target = 2*n+2 ∧ evenControl code ∧
    Rel (evenConfig code gap
      (IncrementSelector.blocksBits (before++[n+1]++(fields++List.replicate n 0)++[0]) (2*retained))
      head leftTail) out) ∨
  (∃ n, target = 2*n+3 ∧ oddControl code ∧
    Rel (oddConfig code gap
      (IncrementSelector.blocksBits (before++[n+1]++(fields++List.replicate n 0)++[0,0]) retained)
      head leftTail) out)

theorem pow_reserve (n retained : Nat) :
    2^(n+1)*retained = 2^n*(2*retained) := by
  simp only [Nat.pow_succ]
  ac_rfl

/-- Every natural operand completes the literal half instruction from a clean
root in finite positive time without an event. The input explicitly provides
`target/2` blank cells before an arbitrary high suffix. The branch theorem
specifies the complete destination and the correct parity control path. -/
theorem root_half_complete (code : List Bool) (gap target : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target])
          (suffixBits fields (2^(target/2)*retained))))) physical) :
    ∃ steps, 0 < steps ∧
      Result code gap target before fields head leftTail retained
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  cases target with
  | zero =>
    simp only [Nat.zero_div,Nat.pow_zero,Nat.one_mul] at hrel
    have h := HalfEven.bound_root_zero_returns_root_physical code gap before fields hwalk
      head leftTail retained physical hrel
    dsimp only at h
    refine ⟨_,h.2.2.2,Or.inl ⟨rfl,h.1,h.2.1⟩,h.2.2.1⟩
  | succ target =>
    cases target with
    | zero =>
      simp only [show 1/2 = 0 by decide,Nat.pow_zero,Nat.one_mul] at hrel
      have h := HalfOne.bound_root_one_returns_root_physical code gap before fields hwalk
        head leftTail retained physical hrel
      dsimp only at h
      refine ⟨_,h.2.2.2,Or.inr (Or.inl ⟨rfl,h.1,h.2.1⟩),h.2.2.1⟩
    | succ k =>
      by_cases heven : k % 2 = 0
      · let n := k/2
        have hk : k = 2*n := by dsimp [n]; omega
        have ht : k+1+1 = 2*n+2 := by omega
        have hd : (2*n+2)/2 = n+1 := by omega
        rw [ht,hd,pow_reserve] at hrel
        have h := HalfEvenPositive.bound_root_returns_root_physical code gap n before fields hwalk
          head leftTail (2*retained) physical hrel
        dsimp only at h
        refine ⟨_,h.2.2.2,Or.inr (Or.inr (Or.inl ⟨n,?_,h.1,h.2.1⟩)),h.2.2.1⟩
        omega
      · let n := k/2
        have hk : k = 2*n+1 := by dsimp [n]; omega
        have ht : k+1+1 = 2*n+3 := by omega
        have hd : (2*n+3)/2 = n+1 := by omega
        rw [ht,hd,pow_reserve] at hrel
        have h := HalfOdd.bound_root_odd_returns_root_physical code gap n before fields hwalk
          head leftTail retained physical hrel
        dsimp only at h
        refine ⟨_,h.2.2.2.2,Or.inr (Or.inr (Or.inr ⟨n,?_,h.2.1,h.2.2.1⟩)),h.2.2.2.1⟩
        omega

end Shared.PNP.Record285.HalfComplete
