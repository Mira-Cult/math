import Shared.Beeping.NPcoNP.GraphCandidate284Shard00
import Shared.Beeping.NPcoNP.GraphCandidate284Shard01
import Shared.Beeping.NPcoNP.GraphCandidate284Shard02
import Shared.Beeping.NPcoNP.GraphCandidate284Shard03
import Shared.Beeping.NPcoNP.GraphCandidate284Shard04
import Shared.Beeping.NPcoNP.GraphCandidate284Shard05
import Shared.Beeping.NPcoNP.GraphCandidate284Shard06
import Shared.Beeping.NPcoNP.GraphCandidate284Shard07
import Shared.Beeping.NPcoNP.GraphCandidate284Shard08
import Shared.Beeping.NPcoNP.GraphCandidate284Shard09
import Shared.Beeping.NPcoNP.GraphCandidate284Shard10
import Shared.Beeping.NPcoNP.GraphCandidate284Shard11
import Shared.Beeping.NPcoNP.GraphCandidate284Shard12
import Shared.Beeping.NPcoNP.GraphCandidate284Shard13
import Shared.Beeping.NPcoNP.GraphCandidate284Shard14
import Shared.Beeping.NPcoNP.GraphCandidate284Shard15
import Shared.Beeping.NPcoNP.GraphCandidate284Shard16
import Shared.Beeping.NPcoNP.GraphCandidate284Shard17
import Shared.Beeping.NPcoNP.GraphCandidate284Shard18

/-! Coverage of the two literal data objects; the grammar and physical
machine bindings remain open. -/
namespace Shared.Beeping.NPcoNP.GraphCandidate284Coverage
open Shared.Beeping.NPcoNP.GraphCandidate284
open Shared.Beeping.NPcoNP.GraphExtended284
open Shared.Beeping.NPcoNP.Parent290Coalesced

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem all_rows (i : Fin 185) : rowMatches graph target i = true := by
  fin_cases i
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row000
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row001
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row002
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row003
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row004
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row005
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row006
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row007
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row008
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard00.row009
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row010
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row011
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row012
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row013
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row014
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row015
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row016
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row017
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row018
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard01.row019
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row020
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row021
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row022
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row023
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row024
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row025
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row026
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row027
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row028
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard02.row029
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row030
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row031
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row032
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row033
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row034
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row035
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row036
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row037
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row038
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard03.row039
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row040
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row041
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row042
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row043
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row044
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row045
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row046
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row047
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row048
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard04.row049
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row050
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row051
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row052
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row053
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row054
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row055
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row056
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row057
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row058
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard05.row059
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row060
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row061
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row062
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row063
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row064
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row065
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row066
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row067
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row068
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard06.row069
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row070
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row071
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row072
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row073
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row074
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row075
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row076
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row077
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row078
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard07.row079
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row080
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row081
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row082
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row083
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row084
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row085
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row086
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row087
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row088
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard08.row089
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row090
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row091
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row092
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row093
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row094
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row095
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row096
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row097
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row098
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard09.row099
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row100
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row101
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row102
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row103
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row104
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row105
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row106
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row107
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row108
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard10.row109
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row110
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row111
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row112
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row113
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row114
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row115
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row116
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row117
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row118
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard11.row119
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row120
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row121
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row122
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row123
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row124
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row125
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row126
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row127
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row128
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard12.row129
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row130
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row131
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row132
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row133
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row134
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row135
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row136
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row137
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row138
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard13.row139
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row140
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row141
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row142
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row143
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row144
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row145
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row146
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row147
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row148
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard14.row149
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row150
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row151
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row152
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row153
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row154
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row155
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row156
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row157
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row158
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard15.row159
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row160
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row161
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row162
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row163
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row164
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row165
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row166
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row167
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row168
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard16.row169
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row170
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row171
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row172
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row173
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row174
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row175
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row176
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row177
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row178
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard17.row179
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard18.row180
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard18.row181
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard18.row182
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard18.row183
  · exact Shared.Beeping.NPcoNP.GraphCandidate284Shard18.row184

theorem graph_matches : graphMatches graph target = true := by
  unfold graphMatches
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro i _
  exact all_rows i

theorem agrees : graph.rows.size = 185 ∧ graph.entry = target.start.val ∧
    ∀ i : Fin 185, ∃ row, graph.rows[i.val]? = some row ∧
      decode row = some target.code[i] := target_sound graph graph_matches

end Shared.Beeping.NPcoNP.GraphCandidate284Coverage
