import Shared.Beeping.NPcoNP.Table284LineData

/-! Kernel checks for newline-free data lines in one finite chunk. -/
namespace Shared.Beeping.NPcoNP.Table284SourceLines
open Shared.Beeping.NPcoNP.Table284LineData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem clean10 : lines10.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean11 : lines11.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean12 : lines12.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean13 : lines13.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean14 : lines14.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean15 : lines15.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean16 : lines16.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean17 : lines17.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean18 : lines18.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean19 : lines19.all (fun line => decide ('\n' ∉ line)) = true := by decide

end Shared.Beeping.NPcoNP.Table284SourceLines
