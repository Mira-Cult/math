import Shared.ComplexityBridge.TM2StrictCleanup
import Shared.ComplexityBridge.TM2WholePair

namespace Shared.ComplexityBridge.TM2VerifierValidity
open Shared.NPCONP.TM2Verifier Shared.Codes.TM2Program Shared.Codes.TM2Candidate
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2BooleanOutput
open Shared.ComplexityBridge.TM2FiniteBoundary Shared.ComplexityBridge.TM2WholePair
open Shared.ComplexityBridge.TM2Symbols

/-- A good verifier must successfully evaluate the empty witness. This forces
its fixed code, initializer, output index, and Boolean codes to be valid; no
claim is made about runtime reification or the remaining cutoff wrapper. -/
theorem good_has_valid_parameters (v : Verifier) (hgood : ∀ x, test v x = true) :
    ∃ p : Program,
      decodeProgram v.2.1.1 = some p ∧
      let d := inputDataOfRaw v.2.1.2.2
      validInputData d = true ∧ d.main < p.length ∧
      programValid p d.stackCount d.states d.symbols = true ∧
      v.2.2.2.2 < d.stackCount ∧ v.2.2.1 ≠ v.2.2.2.1 := by
  have hterm := ((test_iff v []).1 (hgood [])).2.1 [] (by simp [witnessBound])
  have hempty : (Shared.Codes.TM2PairCandidate.evaluate v.2 [] []).isSome = true := by
    simpa [verify,cutoff] using hterm
  cases he : Shared.Codes.TM2PairCandidate.evaluate v.2 [] [] with
  | none => simp [he] at hempty
  | some b =>
    have hcand : Shared.Codes.TM2CheckedCandidate.candidateValid v.2 = true :=
      ((test_iff v []).1 (hgood [])).1
    cases hp : decodeProgram v.2.1.1 with
    | none => simp [Shared.Codes.TM2CheckedCandidate.candidateValid,hp] at hcand
    | some p =>
      let d := inputDataOfRaw v.2.1.2.2
      obtain ⟨hd, hm, hv, start, r, hs, hr, hout⟩ := pair_numeric_result v.2 p hp [] [] b he
      obtain ⟨start',hs',hstartvalid⟩ := buildStart_valid d (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))) p hd hm
      have heq : start' = start := Option.some.inj (hs'.symm.trans hs)
      subst start'
      simp only [List.length_nil, Nat.zero_add] at hr
      have hrvalid := Shared.Codes.TM2Program.run_safe p d.stackCount d.states d.symbols hv
        (2^v.2.1.2.1) start hstartvalid
      rw [hr] at hrvalid
      have houtidx : v.2.2.2.2 < d.stackCount := extract_stack_in_range r hrvalid.1.2.1 b hout
      have hneq : v.2.2.1 ≠ v.2.2.2.1 := by
        intro h
        simp [extractMemory,extractOutput,decodeStack,h] at hout
      exact ⟨p,rfl,hd,hm,hv,houtidx,hneq⟩

/-- For a real output index, strict finite-stack decoding agrees even when
the numeric output is malformed and therefore defaults to false. -/
theorem strict_related (ks states symbols labels z one out : Nat)
    (r : Result) (c : Turing.TM2.Cfg (fun _ : Fin (ks+1) => Fin (symbols+1))
      (Fin (labels+1)) (Fin (states+1)))
    (hrel : Shared.ComplexityBridge.TM2FiniteReverse.CfgRel ks states symbols labels c (erase r))
    (hout : out < ks) (hhalt : r.label = none) :
    Shared.ComplexityBridge.TM2StrictCleanup.strictAnswer z one (c.stk (Shared.ComplexityBridge.TM2FiniteReverse.clip ks out)) =
      (extractMemory (z,one,out,r.label,r.memory)).getD false := by
  have hidx : (Shared.ComplexityBridge.TM2FiniteReverse.clip ks out).val = out :=
    Shared.ComplexityBridge.TM2FiniteReverse.clip_val ks out (by omega)
  have hstack := hrel.2.2 (Shared.ComplexityBridge.TM2FiniteReverse.clip ks out)
  rw [hidx] at hstack
  change stackFn r.memory out = (c.stk (Shared.ComplexityBridge.TM2FiniteReverse.clip ks out)).map Fin.val at hstack
  rw [Shared.ComplexityBridge.TM2StrictCleanup.strictAnswer_eq, ← hstack]
  simp [extractMemory,extractOutput,hhalt]

set_option backward.isDefEq.respectTransparency false in
/-- The input-driven clocked run and the strict default-false cleanup have
matching finite-core configurations and a polynomial block bound. They remain
two separate runs; a machine-level handoff is not asserted here. -/
theorem pair_halt_then_strict_cleanup (d : InputData) (k : Nat) (p : Program) (output z one : Nat)
    (x w : List Bool) (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (hout : output < d.stackCount)
    (start r : Result) (hstart : buildStart d (BitstringEncoding.bitEncode (x,w)) = some start)
    (hrun : run p ((x.length+w.length+2)^k) start = .halted r) :
    ∃ n ≤ 4*(BitstringEncoding.bitEncode (x,w)).length+8 + k*14*(x.length+w.length+4)^k + (x.length+w.length+2)^k,
      ∃ m ≤ (x.length+w.length+2)^k, ∃ c' flag,
      Shared.ComplexityBridge.TM2FiniteReverse.CfgRel d.stackCount d.states d.symbols p.length c' (erase r) ∧
      runSteps (Shared.ComplexityBridge.TM2PairClock.machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step n
        (Turing.initList (Shared.ComplexityBridge.TM2PairClock.machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol)
          (BitstringEncoding.bitEncode (x,w))) =
      some (Shared.ComplexityBridge.TM2PairClock.runnerEmbed d.stackCount d.states d.symbols k p
        (Shared.ComplexityBridge.TM2PairClock.aux (x.length+w.length+2))
        (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
          (Shared.ComplexityBridge.TM2UnaryClock.embed d.stackCount d.states d.symbols p.length flag
            ((List.replicate ((x.length+w.length+2)^k) true).drop m) c'))) ∧
      ∃ t ≤ (d.stackCount+1)*((BitstringEncoding.bitEncode (x,w)).length +
          (x.length+w.length+2)^k * Shared.ComplexityBridge.TM2StackBound.programDepth p+1)+3,
        runSteps (Shared.ComplexityBridge.TM2StrictCleanup.machine d.stackCount d.states d.symbols d.initialState output z one).step t
          (Shared.ComplexityBridge.TM2StrictCleanup.fetch d.stackCount d.states d.symbols d.initialState output z one c'.var c'.stk) =
        some (Turing.haltList (Shared.ComplexityBridge.TM2StrictCleanup.machine d.stackCount d.states d.symbols d.initialState output z one)
          [(extractMemory (z,one,output,r.label,r.memory)).getD false]) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let fuel := (x.length+w.length+2)^k
  obtain ⟨start',hs,hvalid⟩ := buildStart_valid d bits p hdata hmain
  have heq : start' = start := Option.some.inj (hs.symm.trans hstart)
  subst start'
  obtain ⟨n,hn,m,hm,c',flag,hrel,hl,hclock⟩ :=
    Shared.ComplexityBridge.TM2PairClock.pair_numeric_halt d k p output x w hdata hp start r hstart hvalid hrun
  have hsafe := Shared.Codes.TM2Program.run_safe p d.stackCount d.states d.symbols hp fuel start hvalid
  rw [hrun] at hsafe
  have hb := Shared.ComplexityBridge.TM2StackBound.run_from_input_bound d bits p fuel start hstart
  rw [hrun] at hb
  have hstack := Shared.ComplexityBridge.TM2StackBound.related_stack_bound d.stackCount d.states d.symbols p.length
    c' r hrel (bits.length + fuel*Shared.ComplexityBridge.TM2StackBound.programDepth p) hb
  obtain ⟨t,ht,hclean⟩ := Shared.ComplexityBridge.TM2StrictCleanup.strict_read_and_clean
    d.stackCount d.states d.symbols d.initialState output z one c'.var c'.stk
    (bits.length + fuel*Shared.ComplexityBridge.TM2StackBound.programDepth p) hstack
  have heq' : (decodeStack (z,one,(c'.stk (Shared.ComplexityBridge.TM2FiniteReverse.clip d.stackCount output)).map Fin.val)).getD false =
      (extractMemory (z,one,output,r.label,r.memory)).getD false := by
    rw [← Shared.ComplexityBridge.TM2StrictCleanup.strictAnswer_eq]
    exact strict_related d.stackCount d.states d.symbols p.length z one output r c' hrel hout hsafe.2
  rw [heq'] at hclean
  exact ⟨n,hn,m,hm,c',flag,hrel,hclock,t,ht,hclean⟩

end Shared.ComplexityBridge.TM2VerifierValidity
