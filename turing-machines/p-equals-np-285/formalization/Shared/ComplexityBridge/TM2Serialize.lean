import Shared.ComplexityBridge.TM2ListCodec

set_option backward.isDefEq.respectTransparency false

/-! Serialize any value whose canonical encoding is already the TM2 input:
no decoding or hidden representation is needed, and the outer Boolean-list
encoding is produced by the existing finite list encoder. -/
namespace Shared.ComplexityBridge.TM2Serialize

noncomputable def timeMachine {α : Type} [BitstringEncoding α] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : α → List Bool)
      (BitstringEncoding.bitEncode : List Bool → List Bool) (BitstringEncoding.bitEncode : α → List Bool) where
  tm := Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine.tm
  inputAlphabet := Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine.inputAlphabet
  outputAlphabet := Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine.outputAlphabet
  time := Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine.time
  outputsFun x := Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine.outputsFun (BitstringEncoding.bitEncode x)

theorem isPolyTime {α : Type} [BitstringEncoding α] :
    ComplexityTheory.IsPolyTime (BitstringEncoding.bitEncode : α → List Bool) := ⟨timeMachine⟩
end Shared.ComplexityBridge.TM2Serialize
