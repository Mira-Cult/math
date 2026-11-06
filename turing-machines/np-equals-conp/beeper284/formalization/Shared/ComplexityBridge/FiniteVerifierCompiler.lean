import Shared.Codes.FiniteProgramNumericPolynomial
import Shared.ComplexityBridge.BoundedHardness
import Shared.ComplexityBridge.TM2WholePair

/-! The concrete bounded-pair compiler for canonical polynomial-time
relations. General option-preserving compilation remains a distinct issue. -/
namespace Shared.ComplexityBridge.FiniteVerifierCompiler
open Shared.Codes.TM2Program Shared.Codes.TM2Candidate Shared.Codes.TM2CheckedCandidate
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2BooleanOutput
open Shared.ComplexityBridge.TM2FiniteBoundary Shared.ComplexityBridge.TM2WholePair

/-- A single successful test forces the fixed numeric program, initializer,
and output index to satisfy the hypotheses of the finite-table compiler. -/
theorem successful_parameters (c : Candidate) (b : Bool)
    (heval : Shared.Codes.TM2PairCandidate.evaluate c [] [] = some b) :
    ∃ p : Program,
      decodeProgram c.1.1 = some p ∧
      let d := inputDataOfRaw c.1.2.2
      validInputData d = true ∧ d.main < p.length ∧
      programValid p d.stackCount d.states d.symbols = true ∧ c.2.2.2 < d.stackCount := by
  have hcand : candidateValid c = true := by
    cases hv : candidateValid c with
    | false => simp [Shared.Codes.TM2PairCandidate.evaluate,hv] at heval
    | true => rfl
  cases hp : decodeProgram c.1.1 with
  | none => simp [candidateValid,hp] at hcand
  | some p =>
    let d := inputDataOfRaw c.1.2.2
    obtain ⟨hd,hm,hv,start,r,hs,hr,hout⟩ := pair_numeric_result c p hp [] [] b heval
    obtain ⟨start',hs',hstartvalid⟩ := buildStart_valid d
      (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))) p hd hm
    have heq : start' = start := Option.some.inj (hs'.symm.trans hs)
    subst start'
    simp only [List.length_nil,Nat.zero_add] at hr
    have hrvalid := Shared.Codes.TM2Program.run_safe p d.stackCount d.states d.symbols hv
      (2^c.1.2.1) start hstartvalid
    rw [hr] at hrvalid
    have houtput : c.2.2.2 < d.stackCount := extract_stack_in_range r hrvalid.1.2.1 b hout
    exact ⟨p,rfl,hd,hm,hv,houtput⟩

/-- Every canonical polynomial-time pair relation has an actual valid finite
program and one polynomial clock on the pinned pair encoding. This establishes
`FiniteVerifierCompiler` without asserting the stronger compiler for arbitrary
partial candidates. -/
theorem canonical_finite_verifier_compiler :
    Shared.ComplexityBridge.BoundedHardness.FiniteVerifierCompiler := by
  intro R hR
  obtain ⟨candidate,_,hcorrect⟩ := Shared.Codes.TM2PairCandidate.canonicalPoly_covers R hR
  obtain ⟨p,hdecode,hdata,hmain,hp,hout⟩ := successful_parameters candidate (R ([],[])) (hcorrect [] [])
  have htotal : ∀ x w, ∃ b, Shared.Codes.TM2PairCandidate.evaluate candidate x w = some b := by
    intro x w
    exact ⟨R (x,w),hcorrect x w⟩
  obtain ⟨program,clock,_,h⟩ := Shared.Codes.FiniteProgramNumericPolynomial.compile_checked_if_total
    candidate p hdecode hdata hmain hp hout htotal
  refine ⟨program,clock,?_⟩
  intro x w
  rw [h x w,hcorrect x w]


/-- SAT hardness now requires only the separately stated polynomial-time
    generator obligation. -/
theorem sat_hard_of_generator
    (hgenerator : Shared.ComplexityBridge.BoundedHardness.GeneratorPolyTime) :
    Shared.ComplexityBridge.CNFWitness.SatHard :=
  Shared.ComplexityBridge.BoundedHardness.satHard_of_compiler_and_generator
    canonical_finite_verifier_compiler hgenerator

/-- The two endpoints remain separate and conditional on their own event
    certificates and on the concrete reduction generator's runtime proof. -/
theorem pnp_of_generator {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M)
    (hgenerator : Shared.ComplexityBridge.BoundedHardness.GeneratorPolyTime) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.ComplexityBridge.BoundedHardness.pnp_conditional cert canonical_finite_verifier_compiler hgenerator

theorem npconp_of_generator {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (hgenerator : Shared.ComplexityBridge.BoundedHardness.GeneratorPolyTime) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.ComplexityBridge.BoundedHardness.npconp_conditional cert canonical_finite_verifier_compiler hgenerator

end Shared.ComplexityBridge.FiniteVerifierCompiler
