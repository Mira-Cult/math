import Shared.Beeping.NPcoNP.Source284HardwireCorrect
import Shared.ComplexityBridge.Encodings

/-! A paid first component of the canonical verifier-pair output. For each
fixed input `x`, the finite hardwired source table initializes the exact
canonical first-component bit prefix on a blank right half and preserves an
arbitrary certificate on the left half. The prefix's explicit length is part
of the interface: its final zero delimiter is not recoverable from the numeric
tape half alone.

The table depends on the fixed input; no uniform polynomial construction of
its description is asserted. This is not a witness decoder, witness appender,
full pair-output routine, or physical 284-state refinement. -/
namespace Shared.Beeping.NPcoNP.Source284PairPrefixLoader

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireCorrect

def pairPrefix (x : List Bool) : List Bool :=
  BitstringEncoding.delimit (BitstringEncoding.bitEncode x)

/-- The exact prefix used by Google's canonical pair encoding. -/
theorem pair_bits (x w : List Bool) :
    BitstringEncoding.bitEncode (x,w) = pairPrefix x ++ BitstringEncoding.bitEncode w := by
  rfl

theorem prefix_length (x : List Bool) : (pairPrefix x).length = 6*x.length+1 := by
  simp [pairPrefix, BitstringEncoding.length_delimit,
    Shared.ComplexityBridge.bitstring_list_encoded_length]
  omega

theorem loader_offset (x : List Bool) : offset (pairPrefix x) = 12*x.length+4 := by
  simp [offset, prefix_length]
  omega

/-- The fixed-input finite table writes the canonical pair prefix and returns
to its first bit in exactly the stated number of charged relative steps.
The entire certificate is preserved, including any tagged witness and higher
bits. `original` is an arbitrary continuation table, whose code is not run. -/
theorem relative_prefix (x : List Bool) (original : Nat → Bool → Row)
    (certificate : Nat) :
    run (table (pairPrefix x) original) ⟨certificate,0,some 0⟩ (12*x.length+4) =
      ⟨certificate,value (pairPrefix x),some (12*x.length+4)⟩ := by
  simpa [loader_offset] using loader_run (pairPrefix x) original certificate

/-- The same result for the actual numeric source evaluator. The finite
continuation is assumed closed and nonempty only to bound its encoded rows;
its behavior is not assumed. The encoding's high description tail and the
certificate are arbitrary. -/
theorem source_prefix (x : List Bool) (original : Nat → Bool → Row)
    (n : Nat) (hn : 0 < n) (hc : Closed n original) (certificate tail : Nat) :
    Source284Relative.run (encode (offset (pairPrefix x)+n) (table (pairPrefix x) original) tail)
      (Source284Relative.initial 0 certificate) (12*x.length+4) =
        ⟨certificate,value (pairPrefix x),active (12*x.length+4)⟩ := by
  have hv : Valid (offset (pairPrefix x)+n) ⟨certificate,0,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    dsimp [offset]
    omega
  have hr := run_toSource (offset (pairPrefix x)+n) (table (pairPrefix x) original) tail
    ⟨certificate,0,some 0⟩ (closed (pairPrefix x) original n hn hc) hv (12*x.length+4)
  change Source284Relative.run (encode (offset (pairPrefix x)+n) (table (pairPrefix x) original) tail)
    (Source284Relative.initial 0 certificate) (12*x.length+4) = _ at hr
  rw [hr, relative_prefix]
  rfl

/-- With an empty witness the written prefix is the complete canonical pair
bitstring. The certificate remains arbitrary and is not consumed. -/
theorem prefix_empty_witness (x : List Bool) :
    pairPrefix x = BitstringEncoding.bitEncode (x,([] : List Bool)) := by
  rw [pair_bits]
  change pairPrefix x = pairPrefix x ++ []
  simp

theorem source_empty_witness (x : List Bool) (original : Nat → Bool → Row)
    (n : Nat) (hn : 0 < n) (hc : Closed n original) (certificate tail : Nat) :
    Source284Relative.run (encode (offset (pairPrefix x)+n) (table (pairPrefix x) original) tail)
      (Source284Relative.initial 0 certificate) (12*x.length+4) =
        ⟨certificate,value (BitstringEncoding.bitEncode (x,([] : List Bool))),
          active (12*x.length+4)⟩ := by
  rw [← prefix_empty_witness]
  exact source_prefix x original n hn hc certificate tail

end Shared.Beeping.NPcoNP.Source284PairPrefixLoader
