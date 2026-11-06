import Shared.Beeping.NPcoNP.Source284UnaryWindowLoader
import Shared.Beeping.NPcoNP.Source284CanonicalTaggedWindow
import Shared.Beeping.NPcoNP.Source284FiniteRelativeRows

/-! A real finite source table consumes a prepared unary clock and hands off
to the fixed canonical tagged verifier. The clock and packed input are still
preloaded: preparing them from the original two halves remains open. -/
namespace Shared.Beeping.NPcoNP.Source284UnaryWindowVerifier

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284PackedGuardWindow
open Shared.Beeping.NPcoNP.Source284CutoffCounter (tokens)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-- The existing finite relative-table rows encode exactly the compiler's
sentinel-tail source program. -/
theorem compiled_encode (program : Program) :
    encode (Source284FiniteRelativeRows.rows program).length
      (Source284ListTables.table (Source284FiniteRelativeRows.rows program)) 1 =
        Source284CompileRecords.compile program := by
  unfold encode Source284CompileRecords.compile
  rw [Source284FiniteRelativeRows.records_eq]

/-- The unary pass leaves a sufficiently large zero block on one side and
the supplied packed data on the other. Both high tails are arbitrary. -/
theorem cleared_window (n left packed garbage : Nat) :
    Window n ⟨2^(n+1)*left,packed+2^n*garbage,active 0⟩
      (Source284Relative.initial packed 0) := by
  refine ⟨rfl,?_,?_⟩
  · have hd : 2^n ∣ 2^(n+1)*left := by
      refine ⟨2*left,?_⟩
      rw [pow_succ]
      ring
    simp [Agree,Source284Relative.initial,Nat.mod_eq_zero_of_dvd hd]
  · simp [Agree,Source284Relative.initial,Nat.add_mod]

/-- A fixed finite source table pays the `n+1` token transitions and then
runs the compiled verifier. Any high data outside the `n`-bit window is
permitted, including on the original negative half. -/
theorem prepared_verifier (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (hR : IsPolyTime R) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      (∀ n, Source284WitnessWindow.width (p.eval (2*n+1))+2 ≤ clock.eval n) ∧
      ∀ (input : List Bool) (certificate left garbage extra : Nat),
        let n := clock.eval (Source284Parser.length (value input))
        let m := p.eval (2*Source284Parser.length (value input)+1)
        let packed := value (BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate))
        Source284Relative.accepts
          (Source284UnaryWindowLoader.description (Source284FiniteRelativeRows.rows program).length
            (Source284ListTables.table (Source284FiniteRelativeRows.rows program)) 0)
          (tokens n (packed+2^n*garbage)) left (n+1+(n+extra)) =
            Source284TaggedWitnessCodec.check m (fun w => R (payload input,w)) certificate := by
  obtain ⟨program,clock,hvalid,hbound,hsource⟩ :=
    Source284CanonicalTaggedWindow.source_window_verifier p R hR
  refine ⟨program,clock,hvalid,hbound,?_⟩
  intro input certificate left garbage extra
  dsimp only
  let n := clock.eval (Source284Parser.length (value input))
  let m := p.eval (2*Source284Parser.length (value input)+1)
  let packed := value (BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate))
  let rows := Source284FiniteRelativeRows.rows program
  let verifier := Source284ListTables.table rows
  have hn : 0 < rows.length := by simp [rows]
  have hv : Closed rows.length verifier := Source284FiniteRelativeRows.closed program hvalid
  have hs := Source284UnaryWindowLoader.source_after_tokens rows.length verifier 0 n left
    (packed+2^n*garbage) (n+extra) hn hv
  have hc := compiled_encode program
  change encode rows.length verifier 1 = Source284CompileRecords.compile program at hc
  rw [hc] at hs
  have hwin : Window n ⟨2^(n+1)*left,packed+2^n*garbage,active 0⟩
      (Source284Relative.initial packed 0) := cleared_window n left packed garbage
  have hr := hsource input certificate ⟨2^(n+1)*left,packed+2^n*garbage,active 0⟩ extra hwin
  exact hs.trans hr

/-- If the reference complement lies in canonical NP, a single finite source
table works for every prepared unary-window input. This is not yet a
blank-start beeper or a source loader from the original raw input. -/
theorem reference_prepared (hNP : referenceLanguageᶜ ∈ NP) :
    ∃ (p : Polynomial Nat) (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (i left garbage : Nat),
        let n := clock.eval (Source284Parser.length i)
        let m := p.eval (2*Source284Parser.length i+1)
        ((∃ certificate, certificate < 2^(n+1+n) ∧
          Source284Relative.accepts
            (Source284UnaryWindowLoader.description (Source284FiniteRelativeRows.rows program).length
              (Source284ListTables.table (Source284FiniteRelativeRows.rows program)) 0)
            (tokens n (value (BitstringEncoding.bitEncode (inputBits i.bits,certificateBits m certificate))+
              2^n*garbage)) left (n+1+n) = true) ↔ (!reference i) = true) := by
  obtain ⟨p,R,hR,hwitness⟩ := Source284PrefixVerifier.witness_of_complement_mem_NP hNP
  obtain ⟨program,clock,hvalid,hbound,hsource⟩ := prepared_verifier p R hR
  refine ⟨p,program,clock,hvalid,?_⟩
  intro i left garbage
  dsimp only
  have hvalue : value i.bits = i := Shared.Codes.BinaryAdditionCanonical.value_bits i
  have hcheck (certificate : Nat) :
      Source284Relative.accepts
        (Source284UnaryWindowLoader.description (Source284FiniteRelativeRows.rows program).length
          (Source284ListTables.table (Source284FiniteRelativeRows.rows program)) 0)
        (tokens (clock.eval (Source284Parser.length i))
          (value (BitstringEncoding.bitEncode
            (inputBits i.bits,certificateBits (p.eval (2*Source284Parser.length i+1)) certificate))+
              2^(clock.eval (Source284Parser.length i))*garbage)) left
        (clock.eval (Source284Parser.length i)+1+clock.eval (Source284Parser.length i)) =
          Source284TaggedWitnessCodec.check (p.eval (2*Source284Parser.length i+1))
            (fun w => R (payload i.bits,w)) certificate := by
    have h := hsource i.bits certificate left garbage 0
    simpa only [hvalue,Nat.add_zero] using h
  simp_rw [hcheck]
  rw [Source284TaggedWitnessCodec.clock_search_iff]
  · exact (hwitness i).symm
  · have h := hbound (Source284Parser.length i)
    omega

end Shared.Beeping.NPcoNP.Source284UnaryWindowVerifier
