import Shared.Codes.TM2ScannerSound

/-! The existing finite numeric TM2 code and program decoders are primitive
recursive. The table types in the pinned library are denumerable, which makes
their successful decodings canonical. The scanner decides the domain and the
canonicality proof supplies the encoded result, without executable reification
of arbitrary functions or a runtime oracle. This file does not prove a uniform
interpreter, a bit-cost bound, or a machine-model simulation. -/
namespace Shared.Codes.TM2Primcodable
open Shared.Codes.TM2Statements Shared.Codes.FiniteTables Shared.Codes.TM2Scanner Shared.Codes.TM2ScannerSound

theorem decode₁_canonical {n : Nat} {t : List Nat} (h : decode₁ n = some t) : Encodable.encode t = n := by
  have ht : Denumerable.ofNat (List Nat) n = t := Denumerable.ofNat_of_decode h
  rw [← ht, Denumerable.encode_ofNat]

theorem decode₂_canonical {n : Nat} {t : List (List Nat)} (h : decode₂ n = some t) : Encodable.encode t = n := by
  have ht : Denumerable.ofNat (List (List Nat)) n = t := Denumerable.ofNat_of_decode h
  rw [← ht, Denumerable.encode_ofNat]

theorem tree_tokens {xs q rest} (h : Tree xs q rest) : xs = tokens q ++ rest := by
  induction h with
  | halt xs => rfl
  | goto t xs v ht => simpa [tokens] using congrArg (fun n => 1 :: n :: xs) (decode₁_canonical ht).symm
  | push k t xs v q rest ht child ih => simp [tokens, decode₁_canonical ht, ← ih]
  | peek k t xs v q rest ht child ih => simp [tokens, decode₂_canonical ht, ← ih]
  | pop k t xs v q rest ht child ih => simp [tokens, decode₂_canonical ht, ← ih]
  | load t xs v q rest ht child ih => simp [tokens, decode₁_canonical ht, ← ih]
  | branch t xs v a b mid rest ht left right iha ihb =>
    simp [tokens, decode₁_canonical ht, ← ihb, ← iha, List.append_assoc]

theorem decodeTokens_canonical {xs q} (h : decodeTokens xs = some q) : tokens q = xs := by
  unfold decodeTokens at h
  cases hp : parse xs.length xs with
  | none => simp [hp] at h
  | some p =>
    rcases p with ⟨q',suffix⟩
    cases suffix with
    | cons x suffix => simp [hp] at h
    | nil =>
      simp [hp] at h
      subst q'
      simpa using (tree_tokens (parse_tree xs.length hp)).symm

theorem decode_canonical {n : Nat} {q : Code}
    (h : Shared.Codes.TM2Statements.decode n = some q) : Encodable.encode q = n := by
  change ((Encodable.decode n : Option (List Nat)).bind decodeTokens) = some q at h
  rw [Denumerable.decode_eq_ofNat] at h
  have ht : tokens q = Denumerable.ofNat (List Nat) n := decodeTokens_canonical h
  change Encodable.encode (tokens q) = n
  rw [ht, Denumerable.encode_ofNat]

theorem decode_roundtrip (n : Nat) :
    Encodable.encode (Shared.Codes.TM2Statements.decode n) = if check n then n+1 else 0 := by
  have hh := check_iff_decode n
  cases hd : Shared.Codes.TM2Statements.decode n with
  | none =>
    have hc : check n = false := by
      cases hc : check n <;> simp_all
    simp [hc]
  | some q =>
    have hc : check n = true := hh.mpr ⟨q,hd⟩
    have he := decode_canonical hd
    simp [hc, he]

instance codePrimcodable : Primcodable Code where
  toEncodable := inferInstance
  prim := by
    have h : Primrec (fun n : Nat => if check n then n+1 else 0) := by
      have h := Primrec.cond check_primrec (Primrec.succ : Primrec Nat.succ) (Primrec.const 0)
      apply h.of_eq
      intro n
      cases check n <;> rfl
    apply Primrec.nat_iff.mp
    exact h.of_eq (fun n => (decode_roundtrip n).symm)

theorem decode_primrec : Primrec Shared.Codes.TM2Statements.decode := Primrec.decode

theorem decode_computable : Computable Shared.Codes.TM2Statements.decode := decode_primrec.to_comp

theorem decodeTokens_primrec : Primrec decodeTokens := by
  have h := decode_primrec.comp (Primrec.encode : Primrec (Encodable.encode : List Nat → Nat))
  apply h.of_eq
  intro xs
  change ((Encodable.decode (Encodable.encode xs) : Option (List Nat)).bind decodeTokens) = decodeTokens xs
  simp

theorem decodeProgram_primrec : Primrec Shared.Codes.TM2Program.decodeProgram := Primrec.decode

theorem decodeProgram_computable : Computable Shared.Codes.TM2Program.decodeProgram := decodeProgram_primrec.to_comp

theorem tokens_primrec : Primrec tokens := by
  have h := (Primrec.ofNat (List Nat)).comp (Primrec.encode : Primrec (Encodable.encode : Code → Nat))
  apply h.of_eq
  intro q
  change Denumerable.ofNat (List Nat) (Encodable.encode (tokens q)) = tokens q
  exact Denumerable.ofNat_encode _

example : Shared.Codes.TM2Program.decodeProgram (Encodable.encode ([.halt] : List Code)) =
    some [.halt] := Encodable.encodek _
example : decodeTokens [7] = none := rfl

end Shared.Codes.TM2Primcodable
