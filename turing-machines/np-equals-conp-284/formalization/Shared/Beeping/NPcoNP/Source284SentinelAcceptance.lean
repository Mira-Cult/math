import Shared.Beeping.NPcoNP.Source284SentinelRecords
import Shared.Beeping.NPcoNP.Source284AcceptRecordEquiv

/-! The sentinel placed after a zero-terminated unary description preserves
acceptance for every fixed input, certificate, and clock. The two accepting
runs can have different final tapes. These theorems do not compare larger
clocks, prove a complexity bound, or connect the source to its tape table. -/
namespace Shared.Beeping.NPcoNP.Source284SentinelAcceptance

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284SentinelRecords
open Shared.Codes.BitNumeralCompare

/-- A sentinel above the original code and at least one padding zero leaves
all source-attempt acceptance bits unchanged at every common clock. -/
theorem sentinel_accepts (code : List Bool) (padding input certificate clock : Nat) :
    accepts (2 ^ (code.length + (padding + 1)) + value code) input certificate clock =
      accepts (value code) input certificate clock := by
  obtain ⟨h0, h1⟩ := sentinel_representation code padding
  rw [h1, h0]
  exact (accepts_eq_of_acceptRecordAgreement _ _
    (sentinel_acceptRecordAgreement (records code padding)) input certificate clock).symm

/-- The corresponding finite existential certificate searches agree at the
same supplied clock and certificate bound. -/
theorem sentinel_acceptBound (code : List Bool) (padding input clock bound : Nat) :
    acceptBound (2 ^ (code.length + (padding + 1)) + value code) input clock bound =
      acceptBound (value code) input clock bound := by
  obtain ⟨h0, h1⟩ := sentinel_representation code padding
  rw [h1, h0]
  exact (Shared.Beeping.NPcoNP.Source284Relative.sentinel_acceptBound
    (records code padding) input clock bound).symm

end Shared.Beeping.NPcoNP.Source284SentinelAcceptance
