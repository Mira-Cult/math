import Shared.Beeping.NPcoNP.Source284SATTableParameters
import Shared.Beeping.NPcoNP.Source284TableSize

/-! Finite state and source-bit bounds for the explicit SAT table producer.
These are size bounds, not a runtime proof for `produceRows`. -/
namespace Shared.Beeping.NPcoNP.Source284SATProducerSize

open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284SATTableParameters

theorem rows_length (p : List Bool × (List Bool × EncRows)) :
    (produceRows p).length = 2*p.1.length + 6*p.2.1.length + p.2.2.length + 9 := by
  simp [produceRows,Source284MaterializeRows.rows_length,
    Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
    Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
    Source284CertificateDispatch.width]
  omega

theorem produced_closed (p : List Bool × (List Bool × EncRows))
    (hn : 0 < p.2.2.length)
    (hc : Closed p.2.2.length (Source284ListTables.table (decodeRows p.2.2))) :
    Closed (produceRows p).length (Source284ListTables.table (decodeRows (produceRows p))) := by
  let validator := Source284VerifierHandoff.table p.1 p.2.1.length
    (Source284ListTables.table (decodeRows p.2.2))
  let count := Source284CertificateDispatch.allocated p.1 p.2.1.length + p.2.2.length
  have hv : Closed count validator :=
    Source284VerifierHandoff.closed p.1 p.2.1.length p.2.2.length _ hn hc
  have hf : Closed (count+1) (Source284FacingAdapter.table validator) :=
    Source284FacingAdapter.closed validator count (by dsimp [count]; omega) hv
  exact Source284MaterializeRows.table_closed (count+1) (Source284FacingAdapter.table validator) hf

/-- With a closed nonempty verifier, the unary-record source numeral has an
explicit quadratic bit-size bound in the actual generated row count. -/
theorem source_size (p : List Bool × (List Bool × EncRows))
    (hn : 0 < p.2.2.length)
    (hc : Closed p.2.2.length (Source284ListTables.table (decodeRows p.2.2))) :
    Nat.size (encode (produceRows p).length
      (Source284ListTables.table (decodeRows (produceRows p))) 0) ≤
      1 + 2*(produceRows p).length*(8*(produceRows p).length+8) :=
  Source284TableSize.encode_zero_size_bound _ _ (produced_closed p hn hc)

end Shared.Beeping.NPcoNP.Source284SATProducerSize
