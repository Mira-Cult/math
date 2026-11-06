import Shared.ComplexityBridge.TM2FlattenBlocksTotal
import Shared.ComplexityBridge.TM2ListCodec

namespace Shared.ComplexityBridge.TM2FlattenBlocksCanonical

/-- The total tagged flattening of Google block sequences belongs to the
pinned canonical polynomial-time class. Both the input and output list
encoding adapters are included and charged. -/
theorem decodeResult_isPolyTime :
    ComplexityTheory.IsPolyTime Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult := by
  obtain ⟨first⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool) (id : List Bool → List Bool)
    (id : List Bool → List Bool) Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult
    Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine Shared.ComplexityBridge.TM2FlattenBlocksTotal.rawTimeMachine
  obtain ⟨second⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult (id : List Bool → List Bool)
    first Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine
  exact ⟨second⟩

end Shared.ComplexityBridge.TM2FlattenBlocksCanonical
