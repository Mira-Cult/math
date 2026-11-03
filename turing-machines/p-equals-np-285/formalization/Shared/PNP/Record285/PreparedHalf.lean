import Shared.PNP.Record285.PreparedDecrement

/-! Prepared-marker native-half execution by exact rejoining at the selector. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.PreparedHalf
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (even_bit even_tail suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

theorem root_dispatch_marked (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine code.length (markedRootEntry code head leftTail rightTail) =
      some ⟨halfTerminal i,head,bits (pathLeft code) leftTail,true,rightTail⟩ := by
  have hr := (producer_half_safe code i hwalk).2.1
  have hs := route_scan code treeRoot (halfTerminal i) hr
    (-(code.length:Int)) true rootLeft []
  have hz : -(code.length:Int)+(code.length:Int) = 0 := by omega
  have hh := run_sound code.length
    (rightWord treeRoot (-(code.length:Int)) code true rootLeft [])
    ⟨halfTerminal i,0,code.reverse++rootLeft,true,[]⟩
    (by simpa only [hz] using hs) head leftTail rightTail
  simpa only [markedRootEntry,denote,Int.add_zero,bits,pathLeft,rootLeft,List.append_assoc] using hh

theorem marked_to_selector (i gap : Nat) (hi : i < 4) (head : Int) (left tail : Nat) :
    silent Record285.machine 1
      ⟨halfTerminal i,head,left,true,2*pushBit (gap+1) true tail⟩ =
      some ⟨HalfPreparation.selector i,head+1,2*left,false,pushBit (gap+1) true tail⟩ := by
  have hr := (HalfPreparation.terminal_rows i hi).2
  simp only [silent,PhysicalNumeric.step,hr,Bool.false_eq_true,if_false,bitVal,if_false,
    Nat.add_zero,even_bit,even_tail]

/-- Any existing clean-root silent execution that passes the selector can be
rejoined from the marked root, preserving its complete final configuration. -/
theorem rejoin_clean_execution (code : List Bool) (gap i : Nat)
    (hwalk : walk 162 code = some (.half i)) (head : Int) (leftTail tail : Nat)
    (steps : Nat) (out : PhysicalNumeric.Config 285)
    (hsteps : code.length+(2*gap+5)+pathCost code ≤ steps)
    (hfull : silent Record285.machine steps
      (rootEntry code head leftTail (2*runPattern false gap true tail)) = some out) :
    silent Record285.machine (code.length+1+(steps-(code.length+(2*gap+5)+pathCost code)))
      (markedRootEntry code head leftTail (2*pushBit (gap+1) true tail)) = some out := by
  let a := code.length+(2*gap+5)+pathCost code
  let b := steps-a
  let mid : PhysicalNumeric.Config 285 :=
    ⟨HalfPreparation.selector i,head+1,2*bits (pathLeft code) leftTail,
      false,pushBit (gap+1) true tail⟩
  have hd := HalfDispatch.root_dispatch_half code i hwalk head leftTail (2*runPattern false gap true tail)
  have ht := HalfDispatch.terminal_to_selector code i gap hwalk head leftTail tail
  have ha : silent Record285.machine a (rootEntry code head leftTail (2*runPattern false gap true tail)) =
      some mid := by
    dsimp [a,mid]
    rw [show code.length+(2*gap+5)+pathCost code = code.length+((2*gap+5)+pathCost code) by omega,
      silent_add,hd]
    simpa only [Option.bind_some] using ht
  have hr := root_dispatch_marked code i hwalk head leftTail (2*pushBit (gap+1) true tail)
  have hi := (producer_half_safe code i hwalk).1
  have hm := marked_to_selector i gap hi head (bits (pathLeft code) leftTail) tail
  have hc : silent Record285.machine (code.length+1)
      (markedRootEntry code head leftTail (2*pushBit (gap+1) true tail)) = some mid := by
    rw [silent_add,hr]
    simpa only [Option.bind_some,mid] using hm
  have hs : a+b = steps := by dsimp [a,b]; omega
  rw [← hs] at hfull
  exact PreparedDecrement.silent_rejoin Record285.machine _ _ _ _ a b (code.length+1) ha hfull hc

/-- All four half cases complete from the prepared marker with the same
reserve and the same complete result as the clean-marker theorem. -/
theorem marked_half_complete (code : List Bool) (gap target : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (markedRootEntry code head leftTail
      (2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target])
          (suffixBits fields (2^(target/2)*retained))))) physical) :
    ∃ steps, 0 < steps ∧
      HalfComplete.Result code gap target before fields head leftTail retained
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  cases target with
  | zero =>
    simp only [Nat.zero_div,Nat.pow_zero,Nat.one_mul] at hrel
    have he := HalfEven.root_zero_returns_root code gap before fields hwalk head leftTail retained
    dsimp only at he
    have hr := rejoin_clean_execution code gap before.length hwalk head leftTail
      (2*IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained))
      _ _ (by omega) he
    have hp := silent_physical Record285.machine _ physical hrel _ _ hr
    have hc := HalfEven.half_control_preserves_root code before.length hwalk
    exact ⟨_,by omega,Or.inl ⟨rfl,hc.2.2.1,hp.1⟩,hp.2⟩
  | succ target =>
    cases target with
    | zero =>
      simp only [show 1/2 = 0 by decide,Nat.pow_zero,Nat.one_mul] at hrel
      have he := HalfOne.root_one_returns_root code gap before fields hwalk head leftTail retained
      dsimp only at he
      have hr := rejoin_clean_execution code gap before.length hwalk head leftTail
        (2*IncrementSelector.blocksBits (before++[1]) (suffixBits fields retained))
        _ _ (by omega) he
      have hp := silent_physical Record285.machine _ physical hrel _ _ hr
      have hz := HalfOdd.half_path_zero code before.length hwalk
      have hc := return_after_zero code.reverse (by simpa using hz)
      exact ⟨_,by omega,Or.inr (Or.inl ⟨rfl,hc,hp.1⟩),hp.2⟩
    | succ k =>
      by_cases heven : k % 2 = 0
      · let n := k/2
        have hk : k = 2*n := by dsimp [n]; omega
        have ht : k+1+1 = 2*n+2 := by omega
        have hd : (2*n+2)/2 = n+1 := by omega
        rw [ht,hd,HalfComplete.pow_reserve] at hrel
        have he := HalfEvenPositive.root_returns_root code gap n before fields hwalk
          head leftTail (2*retained)
        dsimp only at he
        have hr := rejoin_clean_execution code gap before.length hwalk head leftTail
          (2*IncrementSelector.blocksBits (before++[2*n+2]) (suffixBits fields (2^n*(2*retained))))
          _ _ (by omega) he
        have hp := silent_physical Record285.machine _ physical hrel _ _ hr
        have hc := HalfEven.half_control_preserves_root code before.length hwalk
        refine ⟨_,by omega,Or.inr (Or.inr (Or.inl ⟨n,?_,hc.2.2.1,hp.1⟩)),hp.2⟩
        omega
      · let n := k/2
        have hk : k = 2*n+1 := by dsimp [n]; omega
        have ht : k+1+1 = 2*n+3 := by omega
        have hd : (2*n+3)/2 = n+1 := by omega
        rw [ht,hd,HalfComplete.pow_reserve] at hrel
        have he := HalfOdd.root_odd_returns_root code gap n before fields hwalk head leftTail retained
        dsimp only at he
        have hr := rejoin_clean_execution code gap before.length hwalk head leftTail
          (2*IncrementSelector.blocksBits (before++[2*n+3]) (suffixBits fields (2^n*(2*retained))))
          _ _ (by omega) he
        have hp := silent_physical Record285.machine _ physical hrel _ _ hr
        have hz := HalfOdd.half_path_zero code before.length hwalk
        have hc := return_after_zero code.reverse (by simpa using hz)
        refine ⟨_,by omega,Or.inr (Or.inr (Or.inr ⟨n,?_,hc,hp.1⟩)),hp.2⟩
        omega

/-- Either stated marker layout completes the half action and preserves its
full parity-dependent result. -/
theorem half_both_markers (code : List Bool) (gap target : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (marker : Bool)
    (head : Int) (leftTail rightTail retained : Nat)
    (hlayout : rightTail = if marker then
      2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target])
          (suffixBits fields (2^(target/2)*retained)))
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target])
          (suffixBits fields (2^(target/2)*retained))))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps, 0 < steps ∧
      HalfComplete.Result code gap target before fields head leftTail retained
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  cases marker with
  | false =>
    simp only [Bool.false_eq_true,if_false] at hlayout
    rw [hlayout] at hrel
    exact HalfComplete.root_half_complete code gap target before fields hwalk head leftTail retained physical hrel
  | true =>
    simp only [if_true] at hlayout
    rw [hlayout] at hrel
    exact marked_half_complete code gap target before fields hwalk head leftTail retained physical hrel

theorem half_then_dispatch (code : List Bool) (gap target : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (marker : Bool)
    (head : Int) (leftTail rightTail retained : Nat)
    (hlayout : rightTail = if marker then
      2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target])
          (suffixBits fields (2^(target/2)*retained)))
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target])
          (suffixBits fields (2^(target/2)*retained))))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps, 0 < steps ∧
      HalfComplete.Result code gap target before fields head leftTail retained
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      HalfComplete.NextDispatch ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨steps,hpos,hresult,hquiet⟩ := half_both_markers code gap target before fields
    hwalk marker head leftTail rightTail retained hlayout physical hrel
  exact ⟨steps,hpos,hresult,
    HalfComplete.result_dispatch code gap target before fields head leftTail retained _ hresult,hquiet⟩

end Shared.PNP.Record285.PreparedHalf
