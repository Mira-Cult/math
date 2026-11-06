import Shared.Beeping.NPcoNP.Parent290OwnershipCoverage
import Shared.Beeping.NPcoNP.Parent290MaskCoverage
import Shared.Beeping.NPcoNP.Parent290MaskLocal
import Shared.Beeping.NPcoNP.CoalescingEvents

/-! A mechanically translated 12-register target for the generated literal
15-register program. No identity with the external producer grammar or the
284-state physical table is claimed. -/
namespace Shared.Beeping.NPcoNP.Parent290Coalesced
open PASoundness
open Shared.Beeping.NPcoNP.CoalescingAlgebra
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.Parent290MaskData

def target : MaskInvariant.Program 12 185 where
  code := Vector.ofFn fun s => translateInstruction logicalToSuffix program.code[s]
  start := program.start

theorem target_start : target.start = program.start := rfl

theorem target_rows : RowsTranslate logicalToSuffix program target := by
  intro s
  simp [target]

theorem reachable_ownership (t : Nat) :
    AccessOK logicalToSuffix (program.system.run t).bank
      program.code[(program.system.run t).state].action :=
  accessOK_on_run logicalToSuffix program masks Parent290MaskCoverage.closed
    initial_covers Parent290OwnershipCoverage.allOwners t

theorem equal_beep_times (t : Nat) :
    program.system.erase.BeepAt t ↔ target.system.erase.BeepAt t :=
  beepAt_iff logicalToSuffix program target target_start target_rows reachable_ownership t

theorem eventual_silence_iff :
    program.system.erase.EventuallySilent ↔ target.system.erase.EventuallySilent :=
  eventuallySilent_iff logicalToSuffix program target target_start target_rows reachable_ownership

theorem infinite_beeps_iff :
    program.system.erase.InfinitelyManyBeeps ↔ target.system.erase.InfinitelyManyBeeps :=
  infinitelyManyBeeps_iff logicalToSuffix program target target_start target_rows reachable_ownership

end Shared.Beeping.NPcoNP.Parent290Coalesced
