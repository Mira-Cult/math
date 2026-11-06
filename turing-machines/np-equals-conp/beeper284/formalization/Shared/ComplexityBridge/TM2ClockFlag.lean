import Shared.ComplexityBridge.TM2AuxSweep

namespace Shared.ComplexityBridge.TM2ClockFlag
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2FiniteReverse Shared.ComplexityBridge.TM2UnaryClock
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation

set_option backward.isDefEq.respectTransparency false in
/-- When every clock tick is true, the flag after a positive number of core
blocks is exactly `some true`. This distinguishes a core halt from the
clock-expiration branch, whose flag is `none`. -/
theorem run_ticks_true (ks states symbols : Nat) (p : Program) (input output main initial : Nat)
    (n fuel : Nat) (c d : (finiteCore ks states symbols p input output main initial).Cfg)
    (flag : Option Bool) (hlen : n ≤ fuel)
    (hrun : runSteps (finiteCore ks states symbols p input output main initial).step n c = some d) :
    runSteps (clocked ks states symbols p input output main initial).step n
      (embed ks states symbols p.length flag (List.replicate fuel true) c) =
    some (embed ks states symbols p.length (if n = 0 then flag else some true)
      ((List.replicate fuel true).drop n) d) := by
  induction n generalizing fuel c flag with
  | zero =>
    change some c = some d at hrun
    cases hrun
    simp [runSteps]
  | succ n ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hlen' : n ≤ fuel := by omega
      rw [runSteps_front] at hrun
      change ((finiteCore ks states symbols p input output main initial).step c).bind
        (runSteps (finiteCore ks states symbols p input output main initial).step n) = some d at hrun
      cases hs : (finiteCore ks states symbols p input output main initial).step c with
      | none => rw [hs] at hrun; contradiction
      | some c' =>
        have hrest : runSteps (finiteCore ks states symbols p input output main initial).step n c' = some d := by
          rw [hs] at hrun
          exact hrun
        rw [runSteps_front]
        change ((clocked ks states symbols p input output main initial).step
          (embed ks states symbols p.length flag (true::List.replicate fuel true) c)).bind
            (runSteps (clocked ks states symbols p input output main initial).step n) = _
        rw [step_tick ks states symbols p input output main initial c c' flag true (List.replicate fuel true) hs]
        have hi := ih fuel c' (some true) hlen' hrest
        cases n <;> simpa [List.replicate_succ] using hi

set_option backward.isDefEq.respectTransparency false in
/-- A genuine bounded numeric halt from an active initial configuration
reaches the halted finite configuration with the clock flag `some true`. -/
theorem numeric_halt_true (ks states symbols : Nat) (p : Program) (input output main initial fuel : Nat)
    (hp : programValid p ks states symbols = true) (start result : Result)
    (hvalid : resultValid ks states symbols p.length start) (hactive : start.label ≠ none)
    (hrun : run p fuel start = .halted result) :
    ∃ n ≤ fuel, ∃ c', CfgRel ks states symbols p.length c' (erase result) ∧ c'.l = none ∧
      runSteps (clocked ks states symbols p input output main initial).step n
        (embed ks states symbols p.length none (List.replicate fuel true)
          (finiteConfig ks states symbols p.length start)) =
      some (embed ks states symbols p.length (some true) ((List.replicate fuel true).drop n) c') := by
  have hfinite := finite_run_from_config ks states symbols p input output main initial hp fuel start hvalid
  rw [hrun] at hfinite
  obtain ⟨n,hn,c',hc,hrel,hh⟩ := hfinite
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    change some (finiteConfig ks states symbols p.length start) = some c' at hc
    have heq := Option.some.inj hc
    rw [← heq] at hh
    cases h : start.label with
    | none => exact hactive h
    | some l => simp [finiteConfig,h] at hh
  refine ⟨n,hn,c',hrel,hh,?_⟩
  have hclock := run_ticks_true ks states symbols p input output main initial n fuel
    (finiteConfig ks states symbols p.length start) c' none hn hc
  simpa [hn0] using hclock

set_option backward.isDefEq.respectTransparency false in
/-- The loaded candidate's genuine halt retains the positive clock flag. -/
theorem loaded_numeric_halt_true (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (p : Program) (output fuel : Nat) (bits : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (start result : Result) (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d bits = some start)
    (hvalid : resultValid d.stackCount d.states d.symbols p.length start)
    (hrun : run p fuel start = .halted result) :
    ∃ n ≤ 2*bits.length+fuel+3, ∃ m ≤ fuel, ∃ c',
      CfgRel d.stackCount d.states d.symbols p.length c' (erase result) ∧ c'.l = none ∧
      runSteps (Shared.ComplexityBridge.TM2LoadedClock.machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step n
        (Shared.ComplexityBridge.TM2LoadedClock.loaderEmbed d.stackCount d.states d.symbols d.inputStack p (List.replicate fuel true) (fun _ => [])
          (clip d.states d.initialState) (Turing.initList (Shared.ComplexityBridge.TM2Loader.loader d.symbols d.falseSymbol d.trueSymbol) bits)) =
        some (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
          (embed d.stackCount d.states d.symbols p.length (some true) ((List.replicate fuel true).drop m) c')) := by
  have hactive : start.label ≠ none := by
    unfold Shared.ComplexityBridge.TM2BooleanInput.buildStart at hstart
    rw [hdata] at hstart
    change some (⟨some d.main,d.initialState,_⟩ : Result) = some start at hstart
    have heq := Option.some.inj hstart
    rw [← heq]
    simp
  obtain ⟨start',hs,a,ha,hload⟩ := Shared.ComplexityBridge.TM2LoadedClock.load_to_clock d p output (List.replicate fuel true) bits hdata
  have heq : start' = start := Option.some.inj (hs.symm.trans hstart)
  subst start'
  obtain ⟨m,hm,c',hc,hh,ht⟩ := numeric_halt_true d.stackCount d.states d.symbols p d.inputStack output
    d.main d.initialState fuel hp start result hvalid hactive hrun
  have ht' := Shared.ComplexityBridge.TM2LoadedClock.clock_run d.stackCount d.states d.symbols p d.inputStack output
    d.main d.initialState d.falseSymbol d.trueSymbol []
    (embed d.stackCount d.states d.symbols p.length none (List.replicate fuel true)
      (finiteConfig d.stackCount d.states d.symbols p.length start)) m
  rw [ht] at ht'
  refine ⟨a+m,by omega,m,hm,c',hc,hh,?_⟩
  rw [runSteps_add,hload]
  exact ht'

set_option backward.isDefEq.respectTransparency false in
/-- The input-driven composed machine distinguishes a genuine halt from a
timeout by its retained clock flag. -/
theorem pair_numeric_halt_true (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (k : Nat) (p : Program) (output : Nat) (x w : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true)
    (hp : programValid p d.stackCount d.states d.symbols = true) (start result : Result)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d (BitstringEncoding.bitEncode (x,w)) = some start)
    (hvalid : resultValid d.stackCount d.states d.symbols p.length start)
    (hrun : run p ((x.length+w.length+2)^k) start = .halted result) :
    ∃ n ≤ 4*(BitstringEncoding.bitEncode (x,w)).length+8 + k*14*(x.length+w.length+4)^k + (x.length+w.length+2)^k,
      ∃ m ≤ (x.length+w.length+2)^k, ∃ c',
        CfgRel d.stackCount d.states d.symbols p.length c' (erase result) ∧ c'.l = none ∧
      runSteps (Shared.ComplexityBridge.TM2PairClock.machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step n
        (Turing.initList (Shared.ComplexityBridge.TM2PairClock.machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol)
          (BitstringEncoding.bitEncode (x,w))) =
      some (Shared.ComplexityBridge.TM2PairClock.runnerEmbed d.stackCount d.states d.symbols k p
        (Shared.ComplexityBridge.TM2PairClock.aux (x.length+w.length+2))
        (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
          (embed d.stackCount d.states d.symbols p.length (some true)
            ((List.replicate ((x.length+w.length+2)^k) true).drop m) c'))) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let b := x.length+w.length+2
  let fuel := b^k
  obtain ⟨a,ha,hsetup⟩ := Shared.ComplexityBridge.TM2PairClock.pair_to_runner d k p output x w
  obtain ⟨t,ht,m,hm,c',hc,hh,hr⟩ := loaded_numeric_halt_true d p output fuel bits hdata hp start result hstart hvalid hrun
  have hr' := Shared.ComplexityBridge.TM2PairClock.runner_run d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol (Shared.ComplexityBridge.TM2PairClock.aux b)
    (Shared.ComplexityBridge.TM2PairClock.runnerStart d p (List.replicate fuel true) bits) t
  change runSteps (Shared.ComplexityBridge.TM2PairClock.Runner d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol).step t (Shared.ComplexityBridge.TM2PairClock.runnerStart d p (List.replicate fuel true) bits) = _ at hr
  rw [hr] at hr'
  refine ⟨a+t,by dsimp [bits,b,fuel] at *; omega,m,hm,c',hc,hh,?_⟩
  rw [runSteps_add,hsetup]
  exact hr'

end Shared.ComplexityBridge.TM2ClockFlag
