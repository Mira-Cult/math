import Shared.Beeping.NPcoNP.Table284LineData

/-! Kernel checks for newline-free data lines in one finite chunk. -/
namespace Shared.Beeping.NPcoNP.Table284SourceLines
open Shared.Beeping.NPcoNP.Table284LineData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem clean00 : lines00.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean01 : lines01.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean02 : lines02.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean03 : lines03.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean04 : lines04.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean05 : lines05.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean06 : lines06.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean07 : lines07.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean08 : lines08.all (fun line => decide ('\n' ∉ line)) = true := by decide
theorem clean09 : lines09.all (fun line => decide ('\n' ∉ line)) = true := by decide

end Shared.Beeping.NPcoNP.Table284SourceLines
