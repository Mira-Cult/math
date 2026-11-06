import Shared.Beeping.NPcoNP.Source284FramedJoinPadding
import Shared.Beeping.NPcoNP.Source284ClearFrameUntagPipeline

/-! Fixed finite serializer table and its state bound, shared by the raw
loader composition and the existing serializer theorem. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedSerializeTable

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Codes.FiniteProgramTaggedLoop (canonical)

abbrev Codec (width : Nat) := Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width

def zero {width : Nat} (enc : Codec width) := Source284EncoderFirstSelection.code enc false
def one {width : Nat} (enc : Codec width) := Source284EncoderFirstSelection.code enc true
def kept {width : Nat} (enc : Codec width) := Source284EncoderMarkerSeed.marker enc
def word {width : Nat} (enc : Codec width) := Source284TaggedMarkerSeed.word enc
def rows {width : Nat} (enc : Codec width) := Source284DetectorProduct.serializerRows (zero enc) (one enc)
def marks {width : Nat} (enc : Codec width) := Source284DetectorProduct.serializerMarks (zero enc) (one enc)
def frameRows (width : Nat) := Source284FiniteRelativeRows.rows (Shared.Codes.FiniteProgramFrameUntag.program width)
def contStates {width : Nat} (enc : Codec width) := Source284DetectorExit.entry (rows enc).length+(frameRows width).length

def continuation {width : Nat} (enc : Codec width) : Nat → Bool → Row :=
  Source284ClearExit.table (rows enc).length (marks enc) (Source284ListTables.table (rows enc))
    (Source284ListTables.table (frameRows width))

def start : Nat := Nat.pair (Source284JoinedEndDetectorTable.index .lead) (Source284FiniteRelativeRows.index 0 true)

def states {width : Nat} (enc : Codec width) :=
  7+(1+(Source284HardwireTable.offset (word enc)+(1+contStates enc)))

def table {width : Nat} (enc : Codec width) : Nat → Bool → Row :=
  Source284JoinedPrefixScan.table (Source284TaggedMarkerSeed.table (word enc) start (continuation enc))

theorem start_lt {width : Nat} (enc : Codec width) : start < contStates enc := by
  have hpos : 0 < (Shared.Codes.FiniteProgramTaggedLoop.program (zero enc) (one enc)).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid _ _)
  have hlogical := Source284SerializerTrace.logical_valid
    (Shared.Codes.FiniteProgramTaggedLoop.program (zero enc) (one enc))
    (canonical [] false (kept enc)).2 true 0 hpos
  have hlift := Source284DetectorProduct.lifted_valid (rows enc).length .lead _ hlogical
  have h := hlift start (by rfl)
  dsimp [contStates,Source284DetectorExit.entry]
  omega

theorem continuation_closed {width : Nat} (enc : Codec width) :
    Closed (contStates enc) (continuation enc) := by
  unfold continuation contStates
  apply Source284ClearExit.closed (rows enc).length (frameRows width).length (marks enc)
    (Source284ListTables.table (rows enc)) _ (by simp [frameRows])
  · exact Source284FiniteRelativeRows.closed _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid _ _)
  · exact Source284FiniteRelativeRows.closed _ (Shared.Codes.FiniteProgramFrameUntag.program_valid width)

theorem closed {width : Nat} (enc : Codec width) : Closed (states enc) (table enc) := by
  unfold states table
  exact Source284JoinedPrefixScan.closed _ _ (by omega)
    (Source284TaggedMarkerSeed.closed (word enc) (contStates enc) start (continuation enc)
      (start_lt enc) (continuation_closed enc))

theorem states_pos {width : Nat} (enc : Codec width) : 0 < states enc := by simp [states]

end Shared.Beeping.NPcoNP.Source284FramedSerializeTable
