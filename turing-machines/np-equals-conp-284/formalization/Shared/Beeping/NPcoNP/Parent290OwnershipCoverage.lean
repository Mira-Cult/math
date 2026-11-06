import Shared.Beeping.NPcoNP.Parent290OwnershipShard00
import Shared.Beeping.NPcoNP.Parent290OwnershipShard01
import Shared.Beeping.NPcoNP.Parent290OwnershipShard02
import Shared.Beeping.NPcoNP.Parent290OwnershipShard03
import Shared.Beeping.NPcoNP.Parent290OwnershipShard04
import Shared.Beeping.NPcoNP.Parent290OwnershipShard05
import Shared.Beeping.NPcoNP.Parent290OwnershipShard06
import Shared.Beeping.NPcoNP.Parent290OwnershipShard07
import Shared.Beeping.NPcoNP.Parent290OwnershipShard08
import Shared.Beeping.NPcoNP.Parent290OwnershipShard09
import Shared.Beeping.NPcoNP.Parent290OwnershipShard10
import Shared.Beeping.NPcoNP.Parent290OwnershipShard11
import Shared.Beeping.NPcoNP.Parent290OwnershipShard12
import Shared.Beeping.NPcoNP.Parent290OwnershipShard13
import Shared.Beeping.NPcoNP.Parent290OwnershipShard14
import Shared.Beeping.NPcoNP.Parent290OwnershipShard15
import Shared.Beeping.NPcoNP.Parent290OwnershipShard16
import Shared.Beeping.NPcoNP.Parent290OwnershipShard17
import Shared.Beeping.NPcoNP.Parent290OwnershipShard18

/-! Finite ownership coverage for the generated literal program.
Producer, coalesced graph and physical machine bindings remain open. -/
namespace Shared.Beeping.NPcoNP.Parent290OwnershipCoverage
open CoalescingAlgebra Coalescing284Map Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem allChecks (s : Fin 185) :
    maskAccessCheck logicalToSuffix (masks s) program.code[s].action = true := by
  fin_cases s
  · exact Parent290OwnershipShard00.row000
  · exact Parent290OwnershipShard00.row001
  · exact Parent290OwnershipShard00.row002
  · exact Parent290OwnershipShard00.row003
  · exact Parent290OwnershipShard00.row004
  · exact Parent290OwnershipShard00.row005
  · exact Parent290OwnershipShard00.row006
  · exact Parent290OwnershipShard00.row007
  · exact Parent290OwnershipShard00.row008
  · exact Parent290OwnershipShard00.row009
  · exact Parent290OwnershipShard01.row010
  · exact Parent290OwnershipShard01.row011
  · exact Parent290OwnershipShard01.row012
  · exact Parent290OwnershipShard01.row013
  · exact Parent290OwnershipShard01.row014
  · exact Parent290OwnershipShard01.row015
  · exact Parent290OwnershipShard01.row016
  · exact Parent290OwnershipShard01.row017
  · exact Parent290OwnershipShard01.row018
  · exact Parent290OwnershipShard01.row019
  · exact Parent290OwnershipShard02.row020
  · exact Parent290OwnershipShard02.row021
  · exact Parent290OwnershipShard02.row022
  · exact Parent290OwnershipShard02.row023
  · exact Parent290OwnershipShard02.row024
  · exact Parent290OwnershipShard02.row025
  · exact Parent290OwnershipShard02.row026
  · exact Parent290OwnershipShard02.row027
  · exact Parent290OwnershipShard02.row028
  · exact Parent290OwnershipShard02.row029
  · exact Parent290OwnershipShard03.row030
  · exact Parent290OwnershipShard03.row031
  · exact Parent290OwnershipShard03.row032
  · exact Parent290OwnershipShard03.row033
  · exact Parent290OwnershipShard03.row034
  · exact Parent290OwnershipShard03.row035
  · exact Parent290OwnershipShard03.row036
  · exact Parent290OwnershipShard03.row037
  · exact Parent290OwnershipShard03.row038
  · exact Parent290OwnershipShard03.row039
  · exact Parent290OwnershipShard04.row040
  · exact Parent290OwnershipShard04.row041
  · exact Parent290OwnershipShard04.row042
  · exact Parent290OwnershipShard04.row043
  · exact Parent290OwnershipShard04.row044
  · exact Parent290OwnershipShard04.row045
  · exact Parent290OwnershipShard04.row046
  · exact Parent290OwnershipShard04.row047
  · exact Parent290OwnershipShard04.row048
  · exact Parent290OwnershipShard04.row049
  · exact Parent290OwnershipShard05.row050
  · exact Parent290OwnershipShard05.row051
  · exact Parent290OwnershipShard05.row052
  · exact Parent290OwnershipShard05.row053
  · exact Parent290OwnershipShard05.row054
  · exact Parent290OwnershipShard05.row055
  · exact Parent290OwnershipShard05.row056
  · exact Parent290OwnershipShard05.row057
  · exact Parent290OwnershipShard05.row058
  · exact Parent290OwnershipShard05.row059
  · exact Parent290OwnershipShard06.row060
  · exact Parent290OwnershipShard06.row061
  · exact Parent290OwnershipShard06.row062
  · exact Parent290OwnershipShard06.row063
  · exact Parent290OwnershipShard06.row064
  · exact Parent290OwnershipShard06.row065
  · exact Parent290OwnershipShard06.row066
  · exact Parent290OwnershipShard06.row067
  · exact Parent290OwnershipShard06.row068
  · exact Parent290OwnershipShard06.row069
  · exact Parent290OwnershipShard07.row070
  · exact Parent290OwnershipShard07.row071
  · exact Parent290OwnershipShard07.row072
  · exact Parent290OwnershipShard07.row073
  · exact Parent290OwnershipShard07.row074
  · exact Parent290OwnershipShard07.row075
  · exact Parent290OwnershipShard07.row076
  · exact Parent290OwnershipShard07.row077
  · exact Parent290OwnershipShard07.row078
  · exact Parent290OwnershipShard07.row079
  · exact Parent290OwnershipShard08.row080
  · exact Parent290OwnershipShard08.row081
  · exact Parent290OwnershipShard08.row082
  · exact Parent290OwnershipShard08.row083
  · exact Parent290OwnershipShard08.row084
  · exact Parent290OwnershipShard08.row085
  · exact Parent290OwnershipShard08.row086
  · exact Parent290OwnershipShard08.row087
  · exact Parent290OwnershipShard08.row088
  · exact Parent290OwnershipShard08.row089
  · exact Parent290OwnershipShard09.row090
  · exact Parent290OwnershipShard09.row091
  · exact Parent290OwnershipShard09.row092
  · exact Parent290OwnershipShard09.row093
  · exact Parent290OwnershipShard09.row094
  · exact Parent290OwnershipShard09.row095
  · exact Parent290OwnershipShard09.row096
  · exact Parent290OwnershipShard09.row097
  · exact Parent290OwnershipShard09.row098
  · exact Parent290OwnershipShard09.row099
  · exact Parent290OwnershipShard10.row100
  · exact Parent290OwnershipShard10.row101
  · exact Parent290OwnershipShard10.row102
  · exact Parent290OwnershipShard10.row103
  · exact Parent290OwnershipShard10.row104
  · exact Parent290OwnershipShard10.row105
  · exact Parent290OwnershipShard10.row106
  · exact Parent290OwnershipShard10.row107
  · exact Parent290OwnershipShard10.row108
  · exact Parent290OwnershipShard10.row109
  · exact Parent290OwnershipShard11.row110
  · exact Parent290OwnershipShard11.row111
  · exact Parent290OwnershipShard11.row112
  · exact Parent290OwnershipShard11.row113
  · exact Parent290OwnershipShard11.row114
  · exact Parent290OwnershipShard11.row115
  · exact Parent290OwnershipShard11.row116
  · exact Parent290OwnershipShard11.row117
  · exact Parent290OwnershipShard11.row118
  · exact Parent290OwnershipShard11.row119
  · exact Parent290OwnershipShard12.row120
  · exact Parent290OwnershipShard12.row121
  · exact Parent290OwnershipShard12.row122
  · exact Parent290OwnershipShard12.row123
  · exact Parent290OwnershipShard12.row124
  · exact Parent290OwnershipShard12.row125
  · exact Parent290OwnershipShard12.row126
  · exact Parent290OwnershipShard12.row127
  · exact Parent290OwnershipShard12.row128
  · exact Parent290OwnershipShard12.row129
  · exact Parent290OwnershipShard13.row130
  · exact Parent290OwnershipShard13.row131
  · exact Parent290OwnershipShard13.row132
  · exact Parent290OwnershipShard13.row133
  · exact Parent290OwnershipShard13.row134
  · exact Parent290OwnershipShard13.row135
  · exact Parent290OwnershipShard13.row136
  · exact Parent290OwnershipShard13.row137
  · exact Parent290OwnershipShard13.row138
  · exact Parent290OwnershipShard13.row139
  · exact Parent290OwnershipShard14.row140
  · exact Parent290OwnershipShard14.row141
  · exact Parent290OwnershipShard14.row142
  · exact Parent290OwnershipShard14.row143
  · exact Parent290OwnershipShard14.row144
  · exact Parent290OwnershipShard14.row145
  · exact Parent290OwnershipShard14.row146
  · exact Parent290OwnershipShard14.row147
  · exact Parent290OwnershipShard14.row148
  · exact Parent290OwnershipShard14.row149
  · exact Parent290OwnershipShard15.row150
  · exact Parent290OwnershipShard15.row151
  · exact Parent290OwnershipShard15.row152
  · exact Parent290OwnershipShard15.row153
  · exact Parent290OwnershipShard15.row154
  · exact Parent290OwnershipShard15.row155
  · exact Parent290OwnershipShard15.row156
  · exact Parent290OwnershipShard15.row157
  · exact Parent290OwnershipShard15.row158
  · exact Parent290OwnershipShard15.row159
  · exact Parent290OwnershipShard16.row160
  · exact Parent290OwnershipShard16.row161
  · exact Parent290OwnershipShard16.row162
  · exact Parent290OwnershipShard16.row163
  · exact Parent290OwnershipShard16.row164
  · exact Parent290OwnershipShard16.row165
  · exact Parent290OwnershipShard16.row166
  · exact Parent290OwnershipShard16.row167
  · exact Parent290OwnershipShard16.row168
  · exact Parent290OwnershipShard16.row169
  · exact Parent290OwnershipShard17.row170
  · exact Parent290OwnershipShard17.row171
  · exact Parent290OwnershipShard17.row172
  · exact Parent290OwnershipShard17.row173
  · exact Parent290OwnershipShard17.row174
  · exact Parent290OwnershipShard17.row175
  · exact Parent290OwnershipShard17.row176
  · exact Parent290OwnershipShard17.row177
  · exact Parent290OwnershipShard17.row178
  · exact Parent290OwnershipShard17.row179
  · exact Parent290OwnershipShard18.row180
  · exact Parent290OwnershipShard18.row181
  · exact Parent290OwnershipShard18.row182
  · exact Parent290OwnershipShard18.row183
  · exact Parent290OwnershipShard18.row184

theorem allOwners (s : Fin 185) :
    MaskAccessOK logicalToSuffix (masks s) program.code[s].action :=
  maskAccessOK_of_check logicalToSuffix (masks s) program.code[s].action (allChecks s)

end Shared.Beeping.NPcoNP.Parent290OwnershipCoverage
