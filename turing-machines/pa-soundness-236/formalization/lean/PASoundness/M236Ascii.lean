import PASoundness.M236TextEncoding

/-! An exact ASCII-to-UTF-8 bridge for compact file-content checks. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Ascii

/-- Exhaustively checked for the 128 ASCII code points. -/
theorem singleton_fin : ∀ i : Fin 128,
    [Char.ofNat i.val].utf8Encode = ⟨⟨[UInt8.ofNat i.val]⟩⟩ := by decide

theorem singleton (b : UInt8) (hb : b.toNat < 128) :
    [Char.ofNat b.toNat].utf8Encode = ⟨⟨[b]⟩⟩ := by
  have h := singleton_fin ⟨b.toNat, hb⟩
  simpa only [UInt8.ofNat_toNat] using h

/-- ASCII characters re-encode to the original bytes, with no hashing or
external conversion in the proof. -/
theorem encode_list (bs : List UInt8) (h : ∀ b ∈ bs, b.toNat < 128) :
    (bs.map fun b => Char.ofNat b.toNat).utf8Encode = ⟨⟨bs⟩⟩ := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.toNat < 128 := h b (by simp)
    have ht : ∀ b ∈ bs, b.toNat < 128 := by
      intro x hx
      exact h x (by simp [hx])
    simp only [List.map_cons, List.utf8Encode_cons, singleton b hb, ih ht]
    rfl

end PASoundness.M236.Ascii
