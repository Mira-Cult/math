import Shared.Beeping.NPcoNP.Source284SerializerEncoderRun

/-! A single fixed encoder can be spliced into the marked serializer's source
program. The workspace and prepared-input conditions remain explicit. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284FixedSerializerEncoder

open Turing Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (canonical totalCost)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (entry)
open Shared.Beeping.NPcoNP.Source284JoinedFrames (joinedBits)
open Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2 (machine cfg)

/-- The source table has a fixed finite continuation, independent of the input.
When its stated workspace condition holds, it executes the joined-input
encoder through the canonical TM2 handoff. -/
theorem fixed_serializer_encoder :
    letI := machine.kFin
    letI := Source284JoinedEncoderFinitePrefix.alphabet
    letI : Inhabited machine.Λ := ⟨machine.main⟩
    ∃ (width : Nat) (enc : Alphabet machine → List.Vector Bool width)
      (dec : List.Vector Bool width → Alphabet machine)
      (hblank : enc default = List.Vector.replicate width false)
      (next : Program) (bound : Polynomial Nat) (q : Nat),
      (∀ a, dec (enc a) = a) ∧ valid next = true ∧ q < next.length ∧
      ∀ (x w rest : List Bool) (dummy : Bool) (L : List Bool) (rev₀ : Bool)
        (kEncoder kSource : Nat) (actual : Source284Relative.Config),
        (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest →
        kEncoder+bound.eval (joinedBits x w).length ≤
          2*(inputBits machine enc (joinedBits x w)).length+3 →
        let zero := Source284EncoderFirstSelection.code enc false
        let one := Source284EncoderFirstSelection.code enc true
        let kept := Source284EncoderMarkerSeed.marker enc
        let remaining := rest++[dummy]
        let out := kept ++ (processed remaining false).flatMap (Source284EncoderFirstSelection.code enc)
        let N := totalCost zero one remaining false kept
        let program := Shared.Codes.FiniteProgramFrameUntagContinue.program width next
        let rows := Source284FiniteRelativeRows.rows program
        let states := (Source284DetectorProduct.serializerRows zero one).length
        let marks := Source284DetectorProduct.serializerMarks zero one
        let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
        let items := Source284SerializerStrip.items enc remaining
        let last := cfg .done none [] [] (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)))
        ∃ d reference mid,
          2*(joinedBits x w).length+1 ≤ d ∧ d ≤ bound.eval (joinedBits x w).length ∧
          TM2to1.TrCfg last mid ∧
          TM0FiniteProgram.tape reference =
            (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr machine.m))
              (TM1to1.trCfg enc hblank mid)).Tape ∧
          let cost := Shared.Codes.FiniteProgramFrameLoop.totalCost width items+2+
            (2+Shared.Codes.FiniteProgramUntag.cost out.reverse)+2+d
          let clock := N+2+cost
          let description := Source284TableEncode.encode (entry states+rows.length)
            (Source284ClearExit.table states marks original (Source284ListTables.table rows)) 1
          let initialRef := toSource (lifted .lead
            (logical (canonical (remaining++L) false kept).2 rev₀ 0))
          Window (kSource+clock) actual initialRef →
          ∃ actualTape rev revSource,
          Window kEncoder (represented actualTape rev (codeState q rev))
            (represented reference rev (codeState q rev)) ∧
          Window kSource (Source284Relative.run description actual clock)
            (Source284SourceRelocation.lift (entry states)
              (represented actualTape revSource (codeState
                ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q) revSource))) := by
  letI := machine.kFin
  letI := Source284JoinedEncoderFinitePrefix.alphabet
  letI : Inhabited machine.Λ := ⟨machine.main⟩
  obtain ⟨width,enc,dec,hblank,next,bound,q,hinv,hvalid,hq,hprefix⟩ :=
    Source284JoinedEncoderFinitePrefix.encoder_finite_fixed_handoff
  refine ⟨width,enc,dec,hblank,next,bound,q,hinv,hvalid,hq,?_⟩
  intro x w rest dummy L rev₀ kEncoder kSource actual hbody hsize
  dsimp only
  obtain ⟨d,reference,mid,hdlo,hdhi,hrel,htape,hrun⟩ := hprefix x w []
  simp only [List.append_nil] at hdlo hdhi hrel htape hrun
  have hsize' : kEncoder+d ≤ 2*(inputBits machine enc (joinedBits x w)).length+3 := by omega
  refine ⟨d,reference,mid,hdlo,hdhi,hrel,htape,?_⟩
  intro hw
  exact Source284SerializerEncoderRun.serializer_runs_joined_prefix enc x w rest dummy L rev₀
    hbody next hvalid d kEncoder kSource q reference hrun hsize' actual hw

end Shared.Beeping.NPcoNP.Source284FixedSerializerEncoder
