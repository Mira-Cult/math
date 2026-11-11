import Sude.TwinStreaming

/-! Kernel-checkable packed adjacent-clear mask and chunked bit counting.
This is an alternative checker prototype only; no performance claim or
certificate-generator change is made. -/
namespace Sude
noncomputable section

/-- Mask positions i < width where both bits i and i+1 are clear. -/
def twinClearMask (bits width : ℕ) : ℕ :=
  Nat.ldiff (2^width - 1) (bits ||| (bits / 2))

theorem twinClearMask_spec (bits width i : ℕ) :
    (twinClearMask bits width).testBit i =
      (decide (i < width) && !(bits.testBit i || bits.testBit (i + 1))) := by
  simp [twinClearMask, Nat.testBit_ldiff, Nat.testBit_div_two]

/-- Finite population count of the low width bits. -/
def twinPopCountLow (bits width : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, if bits.testBit i then 1 else 0

theorem twin_clear_mask_popcount (bits width : ℕ) :
    twinPopCountLow (twinClearMask bits width) width = streamTwinCount bits width := by
  rw [streamTwinCount_spec]
  unfold twinPopCountLow
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < width := Finset.mem_range.mp hi
  rw [twinClearMask_spec]
  simp only [hi', decide_true, Bool.true_and]
  cases h0 : bits.testBit i <;> cases h1 : bits.testBit (i + 1) <;> simp_all

/-- Population counts split at a bit boundary, without assuming leading bits
are zero. -/
theorem twin_popcount_split (bits a b : ℕ) :
    twinPopCountLow bits (a + b) =
      twinPopCountLow bits a + twinPopCountLow (bits / 2^a) b := by
  unfold twinPopCountLow
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.testBit_div_two_pow]
  simp [Nat.add_comm]

/-- The 16 four-bit counts, packed as four-bit table entries. Its contents
are an untrusted literal checked by the next theorem. -/
def twinNibbleTable : ℕ := 4841987667533046032

def twinNibbleLookup (bits : ℕ) : ℕ :=
  (twinNibbleTable / 16^(bits % 16)) % 16

/-- Exhaustively kernel-check the lookup table against the low-bit definition. -/
theorem twin_nibble_table_correct :
    ∀ x : Fin 16, twinNibbleLookup x.val = twinPopCountLow x.val 4 := by
  decide +kernel

theorem twin_nibble_lookup_correct (bits : ℕ) :
    twinNibbleLookup bits = twinPopCountLow bits 4 := by
  have h := twin_nibble_table_correct ⟨bits % 16, Nat.mod_lt _ (by decide)⟩
  have hlookup : twinNibbleLookup (bits % 16) = twinNibbleLookup bits := by
    simp [twinNibbleLookup]
  have hpop : twinPopCountLow (bits % 16) 4 = twinPopCountLow bits 4 := by
    unfold twinPopCountLow
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < 4 := Finset.mem_range.mp hi
    change (if (bits % 2^4).testBit i then 1 else 0) = _
    rw [Nat.testBit_mod_two_pow]
    simp [hi']
  rw [hlookup, hpop] at h
  exact h

/-- Four-bit chunks plus a small residual tail. -/
def twinNibbleChunks (bits : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => twinNibbleLookup bits + twinNibbleChunks (bits / 16) k

theorem twin_nibble_chunks_correct (bits k : ℕ) :
    twinNibbleChunks bits k = twinPopCountLow bits (4 * k) := by
  induction k generalizing bits with
  | zero => simp [twinNibbleChunks, twinPopCountLow]
  | succ k ih =>
    rw [twinNibbleChunks, twin_nibble_lookup_correct, ih]
    have h := twin_popcount_split bits 4 (4 * k)
    have hwidth : 4 * (k + 1) = 4 + 4 * k := by omega
    rw [hwidth, h]
    norm_num

/-- A chunked low-bit population count that handles every width, including
zero and a nonempty tail shorter than one nibble. -/
def twinChunkedPopCount (bits width : ℕ) : ℕ :=
  twinNibbleChunks bits (width / 4) +
    twinPopCountLow (bits / 16^(width / 4)) (width % 4)

theorem twin_chunked_popcount_correct (bits width : ℕ) :
    twinChunkedPopCount bits width = twinPopCountLow bits width := by
  unfold twinChunkedPopCount
  rw [twin_nibble_chunks_correct]
  have hp : 16^(width / 4) = 2^(4 * (width / 4)) := by
    rw [show (16 : ℕ) = 2^4 by norm_num, ← Nat.pow_mul]
  rw [hp, ← twin_popcount_split]
  congr 1
  exact Nat.div_add_mod width 4

/-- The chunked packed alternative computes the original exact twin count. -/
theorem twin_chunked_clear_count_correct (bits width : ℕ) :
    twinChunkedPopCount (twinClearMask bits width) width = streamTwinCount bits width := by
  rw [twin_chunked_popcount_correct, twin_clear_mask_popcount]

/-- A fixed 8-bit SWAR population count. Its input is reduced to one byte
before use below, and the finite identity is checked by Lean's kernel. -/
def twinByteSwar (x : ℕ) : ℕ :=
  let a := x - ((x >>> 1) &&& 85)
  let b := (a &&& 51) + ((a >>> 2) &&& 51)
  (b + (b >>> 4)) &&& 15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem twin_byte_swar_finite_correct :
    ∀ x : Fin 256, twinByteSwar x.val = twinPopCountLow x.val 8 := by
  decide +kernel

def twinByteCount (bits : ℕ) : ℕ := twinByteSwar (bits % 256)

theorem twin_byte_count_correct (bits : ℕ) :
    twinByteCount bits = twinPopCountLow bits 8 := by
  have h := twin_byte_swar_finite_correct ⟨bits % 256, Nat.mod_lt _ (by decide)⟩
  have hpop : twinPopCountLow (bits % 256) 8 = twinPopCountLow bits 8 := by
    unfold twinPopCountLow
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < 8 := Finset.mem_range.mp hi
    change (if (bits % 2^8).testBit i then 1 else 0) = _
    rw [Nat.testBit_mod_two_pow]
    simp [hi']
  change twinByteCount bits = twinPopCountLow bits 8
  rw [← hpop]
  exact h

/-- Count complete bytes by the checked SWAR identity. -/
def twinByteChunks (bits : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => twinByteCount bits + twinByteChunks (bits / 256) k

theorem twin_byte_chunks_correct (bits k : ℕ) :
    twinByteChunks bits k = twinPopCountLow bits (8 * k) := by
  induction k generalizing bits with
  | zero => simp [twinByteChunks, twinPopCountLow]
  | succ k ih =>
    rw [twinByteChunks, twin_byte_count_correct, ih]
    have h := twin_popcount_split bits 8 (8 * k)
    have hwidth : 8 * (k + 1) = 8 + 8 * k := by omega
    rw [hwidth, h]
    norm_num

/-- Byte chunks followed by the exact residual low-bit count. -/
def twinByteChunkedPopCount (bits width : ℕ) : ℕ :=
  twinByteChunks bits (width / 8) +
    twinPopCountLow (bits / 256^(width / 8)) (width % 8)

theorem twin_byte_chunked_popcount_correct (bits width : ℕ) :
    twinByteChunkedPopCount bits width = twinPopCountLow bits width := by
  unfold twinByteChunkedPopCount
  rw [twin_byte_chunks_correct]
  have hp : 256^(width / 8) = 2^(8 * (width / 8)) := by
    rw [show (256 : ℕ) = 2^8 by norm_num, ← Nat.pow_mul]
  rw [hp, ← twin_popcount_split]
  congr 1
  exact Nat.div_add_mod width 8

/-- The byte-SWAR checker retains the original count, including the final
lookahead bit, for every bit pattern and width. -/
theorem twin_byte_chunked_clear_count_correct (bits width : ℕ) :
    twinByteChunkedPopCount (twinClearMask bits width) width = streamTwinCount bits width := by
  rw [twin_byte_chunked_popcount_correct, twin_clear_mask_popcount]


end
end Sude
