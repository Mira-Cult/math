import Sude.FiniteTwinOddBaseData
import Sude.GeneratedTwinBase.B000
import Sude.GeneratedTwinBase.B001
import Sude.GeneratedTwinBase.B002
import Sude.GeneratedTwinBase.B003
import Sude.GeneratedTwinBase.B004
import Sude.GeneratedTwinBase.B005
import Sude.GeneratedTwinBase.B006
import Sude.GeneratedTwinBase.B007
import Sude.GeneratedTwinBase.B008
import Sude.GeneratedTwinBase.B009
import Sude.GeneratedTwinBase.B010
import Sude.GeneratedTwinBase.B011
import Sude.GeneratedTwinBase.B012
import Sude.GeneratedTwinBase.B013
import Sude.GeneratedTwinBase.B014
import Sude.GeneratedTwinBase.B015
import Sude.GeneratedTwinBase.B016
import Sude.GeneratedTwinBase.B017
import Sude.GeneratedTwinBase.B018
import Sude.GeneratedTwinBase.B019
import Sude.GeneratedTwinBase.B020
import Sude.GeneratedTwinBase.B021
import Sude.GeneratedTwinBase.B022
import Sude.GeneratedTwinBase.B023
import Sude.GeneratedTwinBase.B024
import Sude.GeneratedTwinBase.B025
import Sude.GeneratedTwinBase.B026
import Sude.GeneratedTwinBase.B027
import Sude.GeneratedTwinBase.B028
import Sude.GeneratedTwinBase.B029
import Sude.GeneratedTwinBase.B030
import Sude.GeneratedTwinBase.B031
import Sude.GeneratedTwinBase.B032
import Sude.GeneratedTwinBase.B033
import Sude.GeneratedTwinBase.B034
import Sude.GeneratedTwinBase.B035
import Sude.GeneratedTwinBase.B036
import Sude.GeneratedTwinBase.B037
import Sude.GeneratedTwinBase.B038
import Sude.GeneratedTwinBase.B039
import Sude.GeneratedTwinBase.B040
import Sude.GeneratedTwinBase.B041
import Sude.GeneratedTwinBase.B042
import Sude.GeneratedTwinBase.B043
import Sude.GeneratedTwinBase.B044
import Sude.GeneratedTwinBase.B045
import Sude.GeneratedTwinBase.B046
import Sude.GeneratedTwinBase.B047
import Sude.GeneratedTwinBase.B048
import Sude.GeneratedTwinBase.B049
import Sude.GeneratedTwinBase.B050
import Sude.GeneratedTwinBase.B051
import Sude.GeneratedTwinBase.B052
import Sude.GeneratedTwinBase.B053
import Sude.GeneratedTwinBase.B054

/-! The generated FT base is certified by checked Lucas nodes. -/
namespace Sude
open Sude.Lucas.Generated
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finiteTwinOddBaseBlocks : List (List ℕ) := [
  B000.values,
  B001.values,
  B002.values,
  B003.values,
  B004.values,
  B005.values,
  B006.values,
  B007.values,
  B008.values,
  B009.values,
  B010.values,
  B011.values,
  B012.values,
  B013.values,
  B014.values,
  B015.values,
  B016.values,
  B017.values,
  B018.values,
  B019.values,
  B020.values,
  B021.values,
  B022.values,
  B023.values,
  B024.values,
  B025.values,
  B026.values,
  B027.values,
  B028.values,
  B029.values,
  B030.values,
  B031.values,
  B032.values,
  B033.values,
  B034.values,
  B035.values,
  B036.values,
  B037.values,
  B038.values,
  B039.values,
  B040.values,
  B041.values,
  B042.values,
  B043.values,
  B044.values,
  B045.values,
  B046.values,
  B047.values,
  B048.values,
  B049.values,
  B050.values,
  B051.values,
  B052.values,
  B053.values,
  B054.values
]

theorem finiteTwinOddBase_blocks : finiteTwinOddBase = finiteTwinOddBaseBlocks.flatten := by
  rfl

theorem finiteTwinOddBase_all :
    finiteTwinOddBase.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  rw [finiteTwinOddBase_blocks, List.all_flatten]
  simp only [finiteTwinOddBaseBlocks, List.all_cons, List.all_nil,
    B000.valid,
    B001.valid,
    B002.valid,
    B003.valid,
    B004.valid,
    B005.valid,
    B006.valid,
    B007.valid,
    B008.valid,
    B009.valid,
    B010.valid,
    B011.valid,
    B012.valid,
    B013.valid,
    B014.valid,
    B015.valid,
    B016.valid,
    B017.valid,
    B018.valid,
    B019.valid,
    B020.valid,
    B021.valid,
    B022.valid,
    B023.valid,
    B024.valid,
    B025.valid,
    B026.valid,
    B027.valid,
    B028.valid,
    B029.valid,
    B030.valid,
    B031.valid,
    B032.valid,
    B033.valid,
    B034.valid,
    B035.valid,
    B036.valid,
    B037.valid,
    B038.valid,
    B039.valid,
    B040.valid,
    B041.valid,
    B042.valid,
    B043.valid,
    B044.valid,
    B045.valid,
    B046.valid,
    B047.valid,
    B048.valid,
    B049.valid,
    B050.valid,
    B051.valid,
    B052.valid,
    B053.valid,
    B054.valid,
    Bool.true_and]

end Sude
