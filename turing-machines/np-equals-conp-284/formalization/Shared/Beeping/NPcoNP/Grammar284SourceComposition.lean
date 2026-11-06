import Shared.Beeping.NPcoNP.GrammarSourceNodeShard00
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard01
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard02
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard03
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard04
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard05
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard06
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard07
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard08
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard09
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard10
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard11
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard12
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard13
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard14
import Shared.Beeping.NPcoNP.GrammarSourceNodeShard15
import Shared.Beeping.NPcoNP.Grammar284SourceChain

/-! Composition of all 160 source-node certificates. This establishes the
fixed-layout character representation, not the correctness of a general JSON
parser or the filesystem SHA-256. -/
namespace Shared.Beeping.NPcoNP.Grammar284.SourceComposition
open Shared.Beeping.NPcoNP.Grammar284.SourceTails
open Shared.Beeping.NPcoNP.Grammar284.SourceRender

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem chain150 : RenderChain (producerGrammar.nodes.toList.drop 150) tail151 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard15.row150
  apply RenderChain.cons
  · exact SourceNodeShard15.row151
  apply RenderChain.cons
  · exact SourceNodeShard15.row152
  apply RenderChain.cons
  · exact SourceNodeShard15.row153
  apply RenderChain.cons
  · exact SourceNodeShard15.row154
  apply RenderChain.cons
  · exact SourceNodeShard15.row155
  apply RenderChain.cons
  · exact SourceNodeShard15.row156
  apply RenderChain.cons
  · exact SourceNodeShard15.row157
  apply RenderChain.cons
  · exact SourceNodeShard15.row158
  apply RenderChain.last
  exact SourceNodeShard15.row159

theorem chain140 : RenderChain (producerGrammar.nodes.toList.drop 140) tail141 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard14.row140
  apply RenderChain.cons
  · exact SourceNodeShard14.row141
  apply RenderChain.cons
  · exact SourceNodeShard14.row142
  apply RenderChain.cons
  · exact SourceNodeShard14.row143
  apply RenderChain.cons
  · exact SourceNodeShard14.row144
  apply RenderChain.cons
  · exact SourceNodeShard14.row145
  apply RenderChain.cons
  · exact SourceNodeShard14.row146
  apply RenderChain.cons
  · exact SourceNodeShard14.row147
  apply RenderChain.cons
  · exact SourceNodeShard14.row148
  apply RenderChain.cons
  · exact SourceNodeShard14.row149
  exact chain150

theorem chain130 : RenderChain (producerGrammar.nodes.toList.drop 130) tail131 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard13.row130
  apply RenderChain.cons
  · exact SourceNodeShard13.row131
  apply RenderChain.cons
  · exact SourceNodeShard13.row132
  apply RenderChain.cons
  · exact SourceNodeShard13.row133
  apply RenderChain.cons
  · exact SourceNodeShard13.row134
  apply RenderChain.cons
  · exact SourceNodeShard13.row135
  apply RenderChain.cons
  · exact SourceNodeShard13.row136
  apply RenderChain.cons
  · exact SourceNodeShard13.row137
  apply RenderChain.cons
  · exact SourceNodeShard13.row138
  apply RenderChain.cons
  · exact SourceNodeShard13.row139
  exact chain140

theorem chain120 : RenderChain (producerGrammar.nodes.toList.drop 120) tail121 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard12.row120
  apply RenderChain.cons
  · exact SourceNodeShard12.row121
  apply RenderChain.cons
  · exact SourceNodeShard12.row122
  apply RenderChain.cons
  · exact SourceNodeShard12.row123
  apply RenderChain.cons
  · exact SourceNodeShard12.row124
  apply RenderChain.cons
  · exact SourceNodeShard12.row125
  apply RenderChain.cons
  · exact SourceNodeShard12.row126
  apply RenderChain.cons
  · exact SourceNodeShard12.row127
  apply RenderChain.cons
  · exact SourceNodeShard12.row128
  apply RenderChain.cons
  · exact SourceNodeShard12.row129
  exact chain130

theorem chain110 : RenderChain (producerGrammar.nodes.toList.drop 110) tail111 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard11.row110
  apply RenderChain.cons
  · exact SourceNodeShard11.row111
  apply RenderChain.cons
  · exact SourceNodeShard11.row112
  apply RenderChain.cons
  · exact SourceNodeShard11.row113
  apply RenderChain.cons
  · exact SourceNodeShard11.row114
  apply RenderChain.cons
  · exact SourceNodeShard11.row115
  apply RenderChain.cons
  · exact SourceNodeShard11.row116
  apply RenderChain.cons
  · exact SourceNodeShard11.row117
  apply RenderChain.cons
  · exact SourceNodeShard11.row118
  apply RenderChain.cons
  · exact SourceNodeShard11.row119
  exact chain120

theorem chain100 : RenderChain (producerGrammar.nodes.toList.drop 100) tail101 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard10.row100
  apply RenderChain.cons
  · exact SourceNodeShard10.row101
  apply RenderChain.cons
  · exact SourceNodeShard10.row102
  apply RenderChain.cons
  · exact SourceNodeShard10.row103
  apply RenderChain.cons
  · exact SourceNodeShard10.row104
  apply RenderChain.cons
  · exact SourceNodeShard10.row105
  apply RenderChain.cons
  · exact SourceNodeShard10.row106
  apply RenderChain.cons
  · exact SourceNodeShard10.row107
  apply RenderChain.cons
  · exact SourceNodeShard10.row108
  apply RenderChain.cons
  · exact SourceNodeShard10.row109
  exact chain110

theorem chain090 : RenderChain (producerGrammar.nodes.toList.drop 90) tail91 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard09.row090
  apply RenderChain.cons
  · exact SourceNodeShard09.row091
  apply RenderChain.cons
  · exact SourceNodeShard09.row092
  apply RenderChain.cons
  · exact SourceNodeShard09.row093
  apply RenderChain.cons
  · exact SourceNodeShard09.row094
  apply RenderChain.cons
  · exact SourceNodeShard09.row095
  apply RenderChain.cons
  · exact SourceNodeShard09.row096
  apply RenderChain.cons
  · exact SourceNodeShard09.row097
  apply RenderChain.cons
  · exact SourceNodeShard09.row098
  apply RenderChain.cons
  · exact SourceNodeShard09.row099
  exact chain100

theorem chain080 : RenderChain (producerGrammar.nodes.toList.drop 80) tail81 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard08.row080
  apply RenderChain.cons
  · exact SourceNodeShard08.row081
  apply RenderChain.cons
  · exact SourceNodeShard08.row082
  apply RenderChain.cons
  · exact SourceNodeShard08.row083
  apply RenderChain.cons
  · exact SourceNodeShard08.row084
  apply RenderChain.cons
  · exact SourceNodeShard08.row085
  apply RenderChain.cons
  · exact SourceNodeShard08.row086
  apply RenderChain.cons
  · exact SourceNodeShard08.row087
  apply RenderChain.cons
  · exact SourceNodeShard08.row088
  apply RenderChain.cons
  · exact SourceNodeShard08.row089
  exact chain090

theorem chain070 : RenderChain (producerGrammar.nodes.toList.drop 70) tail71 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard07.row070
  apply RenderChain.cons
  · exact SourceNodeShard07.row071
  apply RenderChain.cons
  · exact SourceNodeShard07.row072
  apply RenderChain.cons
  · exact SourceNodeShard07.row073
  apply RenderChain.cons
  · exact SourceNodeShard07.row074
  apply RenderChain.cons
  · exact SourceNodeShard07.row075
  apply RenderChain.cons
  · exact SourceNodeShard07.row076
  apply RenderChain.cons
  · exact SourceNodeShard07.row077
  apply RenderChain.cons
  · exact SourceNodeShard07.row078
  apply RenderChain.cons
  · exact SourceNodeShard07.row079
  exact chain080

theorem chain060 : RenderChain (producerGrammar.nodes.toList.drop 60) tail61 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard06.row060
  apply RenderChain.cons
  · exact SourceNodeShard06.row061
  apply RenderChain.cons
  · exact SourceNodeShard06.row062
  apply RenderChain.cons
  · exact SourceNodeShard06.row063
  apply RenderChain.cons
  · exact SourceNodeShard06.row064
  apply RenderChain.cons
  · exact SourceNodeShard06.row065
  apply RenderChain.cons
  · exact SourceNodeShard06.row066
  apply RenderChain.cons
  · exact SourceNodeShard06.row067
  apply RenderChain.cons
  · exact SourceNodeShard06.row068
  apply RenderChain.cons
  · exact SourceNodeShard06.row069
  exact chain070

theorem chain050 : RenderChain (producerGrammar.nodes.toList.drop 50) tail51 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard05.row050
  apply RenderChain.cons
  · exact SourceNodeShard05.row051
  apply RenderChain.cons
  · exact SourceNodeShard05.row052
  apply RenderChain.cons
  · exact SourceNodeShard05.row053
  apply RenderChain.cons
  · exact SourceNodeShard05.row054
  apply RenderChain.cons
  · exact SourceNodeShard05.row055
  apply RenderChain.cons
  · exact SourceNodeShard05.row056
  apply RenderChain.cons
  · exact SourceNodeShard05.row057
  apply RenderChain.cons
  · exact SourceNodeShard05.row058
  apply RenderChain.cons
  · exact SourceNodeShard05.row059
  exact chain060

theorem chain040 : RenderChain (producerGrammar.nodes.toList.drop 40) tail41 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard04.row040
  apply RenderChain.cons
  · exact SourceNodeShard04.row041
  apply RenderChain.cons
  · exact SourceNodeShard04.row042
  apply RenderChain.cons
  · exact SourceNodeShard04.row043
  apply RenderChain.cons
  · exact SourceNodeShard04.row044
  apply RenderChain.cons
  · exact SourceNodeShard04.row045
  apply RenderChain.cons
  · exact SourceNodeShard04.row046
  apply RenderChain.cons
  · exact SourceNodeShard04.row047
  apply RenderChain.cons
  · exact SourceNodeShard04.row048
  apply RenderChain.cons
  · exact SourceNodeShard04.row049
  exact chain050

theorem chain030 : RenderChain (producerGrammar.nodes.toList.drop 30) tail31 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard03.row030
  apply RenderChain.cons
  · exact SourceNodeShard03.row031
  apply RenderChain.cons
  · exact SourceNodeShard03.row032
  apply RenderChain.cons
  · exact SourceNodeShard03.row033
  apply RenderChain.cons
  · exact SourceNodeShard03.row034
  apply RenderChain.cons
  · exact SourceNodeShard03.row035
  apply RenderChain.cons
  · exact SourceNodeShard03.row036
  apply RenderChain.cons
  · exact SourceNodeShard03.row037
  apply RenderChain.cons
  · exact SourceNodeShard03.row038
  apply RenderChain.cons
  · exact SourceNodeShard03.row039
  exact chain040

theorem chain020 : RenderChain (producerGrammar.nodes.toList.drop 20) tail21 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard02.row020
  apply RenderChain.cons
  · exact SourceNodeShard02.row021
  apply RenderChain.cons
  · exact SourceNodeShard02.row022
  apply RenderChain.cons
  · exact SourceNodeShard02.row023
  apply RenderChain.cons
  · exact SourceNodeShard02.row024
  apply RenderChain.cons
  · exact SourceNodeShard02.row025
  apply RenderChain.cons
  · exact SourceNodeShard02.row026
  apply RenderChain.cons
  · exact SourceNodeShard02.row027
  apply RenderChain.cons
  · exact SourceNodeShard02.row028
  apply RenderChain.cons
  · exact SourceNodeShard02.row029
  exact chain030

theorem chain010 : RenderChain (producerGrammar.nodes.toList.drop 10) tail11 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard01.row010
  apply RenderChain.cons
  · exact SourceNodeShard01.row011
  apply RenderChain.cons
  · exact SourceNodeShard01.row012
  apply RenderChain.cons
  · exact SourceNodeShard01.row013
  apply RenderChain.cons
  · exact SourceNodeShard01.row014
  apply RenderChain.cons
  · exact SourceNodeShard01.row015
  apply RenderChain.cons
  · exact SourceNodeShard01.row016
  apply RenderChain.cons
  · exact SourceNodeShard01.row017
  apply RenderChain.cons
  · exact SourceNodeShard01.row018
  apply RenderChain.cons
  · exact SourceNodeShard01.row019
  exact chain020

theorem chain000 : RenderChain (producerGrammar.nodes.toList.drop 0) tail1 tail161 := by
  apply RenderChain.cons
  · exact SourceNodeShard00.row000
  apply RenderChain.cons
  · exact SourceNodeShard00.row001
  apply RenderChain.cons
  · exact SourceNodeShard00.row002
  apply RenderChain.cons
  · exact SourceNodeShard00.row003
  apply RenderChain.cons
  · exact SourceNodeShard00.row004
  apply RenderChain.cons
  · exact SourceNodeShard00.row005
  apply RenderChain.cons
  · exact SourceNodeShard00.row006
  apply RenderChain.cons
  · exact SourceNodeShard00.row007
  apply RenderChain.cons
  · exact SourceNodeShard00.row008
  apply RenderChain.cons
  · exact SourceNodeShard00.row009
  exact chain010

theorem producerChain : RenderChain producerGrammar.nodes.toList tail1 tail161 := by
  exact chain000

theorem footer_eq : footer producerGrammar = tail161 := by rfl

theorem source_to_render : SourceChars.source.toList = render producerGrammar := by
  rw [source_toList]
  unfold render
  rw [footer_eq, nodes_eq_of_chain producerChain]
  rfl

theorem source_eq_serialization :
    SourceChars.source = String.ofList (render producerGrammar) := by
  simpa only [String.ofList_toList] using congrArg String.ofList source_to_render

/-- Every embedded source byte is covered by the UTF-8 encoding of the
fixed-layout rendering. This does not assert a filesystem hash or parser
correctness theorem. -/
theorem source_bytes_to_render :
    SourceChars.source.toByteArray = (render producerGrammar).utf8Encode := by
  rw [← String.utf8Encode_toList, source_to_render]

end Shared.Beeping.NPcoNP.Grammar284.SourceComposition
