import Shared.Beeping.NPcoNP.Table284LineData

/-! Kernel checks for newline-free data lines in one finite chunk. -/
namespace Shared.Beeping.NPcoNP.Table284SourceLines
open Shared.Beeping.NPcoNP.Table284LineData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem clean20 : lines20.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean21 : lines21.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean22 : lines22.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean23 : lines23.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean24 : lines24.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean25 : lines25.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean26 : lines26.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean27 : lines27.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean28 : lines28.all (fun line => decide ('\n' ∉ line)) = true := by decide

end Shared.Beeping.NPcoNP.Table284SourceLines
