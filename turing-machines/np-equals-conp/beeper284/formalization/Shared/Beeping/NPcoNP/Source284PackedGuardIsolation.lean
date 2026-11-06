import Shared.Beeping.NPcoNP.Source284PackedGuardWindow
import Shared.Beeping.NPcoNP.Source284ClockStability

/-! Finite-window isolation for the fixed packed verifier. A prepared source
configuration need only agree with the canonical input on the finite window
that the verifier can visit. Bits outside that window are arbitrary; the
compiled accept and reject sinks preserve the result forever. This does not
construct a loader that prepares the window. -/
namespace Shared.Beeping.NPcoNP.Source284PackedGuardIsolation

open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284CompileRecords
open Shared.Beeping.NPcoNP.Source284FiniteProgramRun
open Shared.Beeping.NPcoNP.Source284PackedGuardWindow
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableRun (run)

/-- A completed valid finite program reaches exactly the corresponding source
accept state or invariant reject sink, including the physical terminal move. -/
theorem compiled_finished (program : Program) (input : List Bool) (clock : Nat) (b : Bool)
    (hv : valid program = true) (hb : bounded program input clock = some b) :
    (Source284Relative.run (compile program) (Source284Relative.initial (value input) 0) clock).state =
      (if b then 0 else rejectState program.length) := by
  have hn : 0 < program.length := by
    cases h : program with
    | nil => simp [h,valid] at hv
    | cons a as => simp
  obtain ⟨t,ht,hr⟩ := (bounded_iff_result program input clock b).1 hb
  have hrun : Shared.Codes.FinitePrograms.run program (Shared.Codes.FinitePrograms.initial input) clock =
      some (.inl b) := Shared.Codes.FinitePrograms.run_result_stable program _ ht hr
  have hrel := Source284FiniteProgramRun.run_related program (closed_of_valid program hv) 0
    (Shared.Codes.FinitePrograms.initial input).2 false hn clock
  have he : (0,(Shared.Codes.FinitePrograms.initial input).2) =
      Shared.Codes.FinitePrograms.initial input := by rfl
  rw [he,hrun,Source284FiniteProgramRun.represented_initial] at hrel
  rw [Source284FiniteTapeStep.value_eq_shared] at hrel
  cases b <;> cases hrel <;> simp_all

/-- If the initial windows agree for the finite verifier clock, then even
arbitrary unrepresented high tape bits cannot change the final result or any
later result: the source has entered one of its two invariant states. -/
theorem compiled_window_stable (program : Program) (input : List Bool) (clock : Nat) (b : Bool)
    (hv : valid program = true) (hb : bounded program input clock = some b)
    (c : Source284Relative.Config)
    (hw : Window clock c (Source284Relative.initial (value input) 0)) (extra : Nat) :
    ((Source284Relative.run (compile program) c (clock+extra)).state == 0) = b := by
  have hw' := Source284Relative.run_window (compile program) clock 0 c
    (Source284Relative.initial (value input) 0) (by simpa using hw)
  have hc : (Source284Relative.run (compile program) c clock).state =
      (if b then 0 else rejectState program.length) := by
    exact hw'.1.trans (compiled_finished program input clock b hv hb)
  rw [Source284Relative.run_add_clock]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    have hs := Source284Relative.run_state_invariant (compile program) (rejectState program.length)
      (sink_step program) _ hc extra
    have hn : rejectState program.length ≠ 0 := Nat.ne_of_gt (state_positive program.length false)
    simp [hs,hn]
  | true =>
    simp only [↓reduceIte] at hc
    rw [Source284Relative.run_absorbing _ _ hc]
    simp [hc]

/-- One fixed finite source program computes the generated checker from any
configuration agreeing with its normalized packed input on a window of the
polynomial cutoff. No assumption is made about either tape beyond that window.
The window must be constructed and charged by a separate finite loader. -/
theorem source_window_checker (p time : Polynomial Nat) (original : EncRows) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (input : List Bool) (certificate : Nat) (c : Source284Relative.Config) (extra : Nat),
        let m := p.eval (2*Source284Parser.length (value input)+1)
        let packed := BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate)
        Window (clock.eval (Source284Parser.length (value input))) c (Source284Relative.initial (value packed) 0) →
        ((Source284Relative.run (compile program) c
          (clock.eval (Source284Parser.length (value input))+extra)).state == 0) =
          Source284ParsedPolynomialGuard.check p time
            (original,(inputBits input,certificateBits m certificate)) := by
  obtain ⟨program,q,hvalid,hcorrect⟩ := Source284PackedGuardCompiler.finite_program p time original
  let bound : Polynomial Nat := Polynomial.C 12 * Polynomial.X +
    Polynomial.C 6 * p.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) + Polynomial.C 25
  let clock : Polynomial Nat := q.comp bound
  refine ⟨program,clock,hvalid,?_⟩
  intro input certificate c extra
  dsimp only
  intro hw
  let m := p.eval (2*Source284Parser.length (value input)+1)
  let packed := BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate)
  have hlen : packed.length ≤ bound.eval (Source284Parser.length (value input)) := by
    have h := packed_length m certificate input
    simpa [packed,bound,m,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
      Polynomial.eval_C,Polynomial.eval_X] using h
  have hclock : q.eval packed.length ≤ clock.eval (Source284Parser.length (value input)) := by
    simp only [clock,Polynomial.eval_comp]
    exact Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono q hlen
  have hsmall := hcorrect (inputBits input) (certificateBits m certificate)
  have hb := Shared.ComplexityBridge.BoundedHardness.bounded_mono program packed
    (q.eval packed.length) (clock.eval (Source284Parser.length (value input)))
    (Source284PackedGuardCompiler.relation p time original (inputBits input,certificateBits m certificate))
    hclock hsmall
  have hh := compiled_window_stable program packed (clock.eval (Source284Parser.length (value input)))
    (Source284PackedGuardCompiler.relation p time original (inputBits input,certificateBits m certificate))
    hvalid hb c hw extra
  exact hh

/-- The same fixed program handles both parsed-prefix cases when a finite
window is supplied. On positive inputs, the supplied verifier must compute
`R` for every decoded alias. The empty prefix is accepted by the cutoff, not
claimed to accept in the single source step required by the outer controller. -/
theorem source_window_realizes (p time : Polynomial Nat) (original : EncRows)
    (R : List Bool × List Bool → Bool)
    (hn : 0 < original.length) (hv : Source284ListTables.valid (decodeRows original) = true)
    (hmatch : ∀ i : Nat, 0 < Source284Parser.length i → ∀ c w,
      Source284TaggedWitnessCodec.decode (p.eval (2*Source284Parser.length i+1)) c = some w →
      (Source284TableRun.run (Source284ListTables.table (decodeRows original))
        ⟨c,i,some 0⟩ (time.eval (Source284Parser.length i)+1)).state.isNone =
          R (Source284RawParse.payload i.bits,w)) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (input : List Bool) (certificate : Nat) (c : Source284Relative.Config) (extra : Nat),
      let m := p.eval (2*Source284Parser.length (value input)+1)
      let packed := BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate)
      Window (clock.eval (Source284Parser.length (value input))) c (Source284Relative.initial (value packed) 0) →
      ((Source284Relative.run (compile program) c
        (clock.eval (Source284Parser.length (value input))+extra)).state == 0) =
        if Source284Parser.length (value input) = 0 then true
        else Source284TaggedWitnessCodec.check m (fun w => R (Source284RawParse.payload input,w)) certificate := by
  obtain ⟨program,clock,hvalid,hcheck⟩ := source_window_checker p time original
  refine ⟨program,clock,hvalid,?_⟩
  intro input certificate c extra
  dsimp only
  intro hw
  let m := p.eval (2*Source284Parser.length (value input)+1)
  have hh := hcheck input certificate c extra hw
  by_cases hz : Source284Parser.length (value input) = 0
  · have hzero : Source284Parser.length (value (inputBits input)) = 0 := by
      rw [input_prefix_length]; exact hz
    have hempty := Source284ParsedPolynomialGuard.check_empty p time
      (original,(inputBits input,certificateBits m certificate)) hzero
    simp only [hz,↓reduceIte]
    simpa only [hz] using hh.trans hempty
  · have hi : 0 < Source284Parser.length (value (inputBits input)) := by
      rw [input_prefix_length]; omega
    have hm : ∀ c w, Source284TaggedWitnessCodec.decode
        (p.eval (2*Source284Parser.length (value (inputBits input))+1)) c = some w →
        (Source284TableRun.run (Source284ListTables.table (decodeRows original))
          ⟨c,value (inputBits input),some 0⟩
          (time.eval (Source284Parser.length (value (inputBits input)))+1)).state.isNone =
            R (Source284RawParse.payload input,w) := by
      intro c w hw
      have h := hmatch (value (inputBits input)) hi c w hw
      simpa only [inputBits_payload] using h
    have hpos := Source284ParsedPolynomialGuard.check_positive p time
      (original,(inputBits input,certificateBits m certificate))
      (fun w => R (Source284RawParse.payload input,w)) hi hn hv hm
    simp only [input_prefix_length,certificateBits_value] at hpos
    dsimp only [m] at hpos
    simp only [tagged_check_mod] at hpos
    simp only [hz,↓reduceIte]
    exact hh.trans hpos

namespace Fixtures

def acceptOne : Program := [((false,true,0,2),(true,true,0,2))]
def rejectOne : Program := [((false,true,0,1),(true,true,0,1))]

/-- Both halves contain a one beyond the observed one-cell window. -/
example (extra : Nat) :
    ((Source284Relative.run (compile acceptOne) ⟨2,2,1⟩ (1+extra)).state == 0) = true := by
  exact compiled_window_stable acceptOne [] 1 true (by decide +kernel) (by decide +kernel)
    ⟨2,2,1⟩ (by
      change 1 = 1 ∧ 2 % 2 = 0 % 2 ∧ 2 % 2 = 0 % 2
      decide +kernel) extra

example (extra : Nat) :
    ((Source284Relative.run (compile rejectOne) ⟨2,2,1⟩ (1+extra)).state == 0) = false := by
  exact compiled_window_stable rejectOne [] 1 false (by decide +kernel) (by decide +kernel)
    ⟨2,2,1⟩ (by
      change 1 = 1 ∧ 2 % 2 = 0 % 2 ∧ 2 % 2 = 0 % 2
      decide +kernel) extra

end Fixtures

end Shared.Beeping.NPcoNP.Source284PackedGuardIsolation
