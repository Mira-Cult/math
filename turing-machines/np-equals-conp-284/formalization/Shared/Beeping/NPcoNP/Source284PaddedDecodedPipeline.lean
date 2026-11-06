import Shared.Beeping.NPcoNP.Source284PaddingBudget

/-! An enlarged prepared unary limit provides the full conservative scratch
window for every old-cutoff witness, including arbitrary high aliases.
Constructing that limit and enforcing the old cutoff in finite source code
are separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284PaddedDecodedPipeline

open Shared.Codes.FiniteProgramTaggedLoop (result)
open Shared.Codes.FiniteProgramFrameLoop (padding)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284OrientedExit (entry)
open Shared.Beeping.NPcoNP.Source284EncoderFirstSelection (code)
open Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed (marker)
open Shared.Beeping.NPcoNP.Source284DecodedTaggedPipeline
open Shared.Beeping.NPcoNP.Source284PaddingBudget (paddedLimit)

/-- Every old-cutoff witness accepted by the enlarged decoder reaches the
stripped output window, even with arbitrary high certificate and input suffixes.
The enlarged unary limit is part of the input and is not generated for free. -/
theorem padded_decoded_to_stripped_window {width : Nat} (enc : Codec width)
    (original certificate input : Nat) (w rest : List Bool) (k : Nat)
    (hdec : Source284TaggedWitnessCodec.decode
      (paddedLimit width (Source284RawParse.payload input.bits).length original k) certificate = some w)
    (hw : w.length ≤ original)
    (hbody : (Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).reverse = false::rest) :
    let limit := paddedLimit width (Source284RawParse.payload input.bits).length original k
    ∃ witnessSuffix inputSuffix,
      certificate = 4*Source284Parser.encodeFrame w witnessSuffix ∧
      input = Source284Parser.encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∃ rev', Window k
        (Source284Relative.run (description enc)
          (Source284Relative.initial certificate
            (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
          (prefixCost limit input w+
            ((Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w).length+
              (seedCost enc+clock enc rest))))
        (let remaining := rest++[true]
         let b := (result (code enc false) (code enc true) remaining false (marker enc)).1
         let L := (inputSuffix/4).bits
         let out := marker enc ++ (processed remaining false).flatMap (code enc)
         Source284SourceRelocation.lift 782
          (Source284SourceRelocation.lift (7+seedCost enc)
           (Source284SourceRelocation.lift (entry (serializerStates enc))
            (represented (tapeAt (cursor b L out).2
              ((cursor b L out).1::false::false::padding (processed remaining false).length [false,false]))
              rev' (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev'))))) := by
  apply decoded_to_stripped_window enc _ certificate input w rest k hdec hbody
  exact Source284PaddingBudget.padding_sufficient enc _ w rest original k hbody hw

end Shared.Beeping.NPcoNP.Source284PaddedDecodedPipeline
