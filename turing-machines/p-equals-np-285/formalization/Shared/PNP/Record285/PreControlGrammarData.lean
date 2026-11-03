import Shared.PNP.Record285.ProjectionGrammarText

namespace Shared.PNP.Record285.PreControlGrammar
open Shared.PNP.Record285.Grammar

open Shared.PNP.Record285.ProducerGrammar
def literal : String := include_str "producer-pre-control.json"

def entries0 : List Entry := [((.dec 13, .cont 1), false), ((.dec 14, .cont 1), false), ((.dec 15, .cont 1), false), ((.dec 16, .cont 1), false)]
def entries1 : List Entry := [((.inc 17, .inc 4), false), ((.node 4, .cont 2), false), ((.dec 14, .node 5), false), ((.inc 14, .cont 2), false)]
def entries2 : List Entry := [((.dec 4, .node 7), false), ((.node 6, .node 8), false), ((.dec 18, .cont 1), false), ((.inc 18, .cont 2), false)]
def entries3 : List Entry := [((.dec 17, .node 11), false), ((.dec 19, .cont 1), false), ((.dec 2, .cont 1), false), ((.dec 3, .cont 1), false)]
def entries4 : List Entry := [((.dec 13, .node 5), false), ((.inc 13, .cont 2), false), ((.dec 4, .node 17), false), ((.dec 20, .cont 1), false)]
def entries5 : List Entry := [((.inc 20, .cont 2), false), ((.dec 17, .node 20), false), ((.dec 18, .node 5), false), ((.dec 4, .node 11), false)]
def entries6 : List Entry := [((.dec 0, .cont 1), false), ((.inc 0, .cont 2), false), ((.dec 17, .node 25), false), ((.half 0, .inc 3), false)]
def entries7 : List Entry := [((.inc 5, .inc 4), false), ((.node 28, .cont 2), false), ((.dec 14, .node 29), false), ((.node 30, .node 8), false)]
def entries8 : List Entry := [((.dec 15, .node 29), false), ((.inc 15, .cont 2), false), ((.dec 4, .node 33), false), ((.node 32, .node 34), false)]
def entries9 : List Entry := [((.dec 1, .cont 1), false), ((.inc 1, .cont 2), false), ((.dec 5, .node 37), false), ((.half 1, .cont 1), false)]
def entries10 : List Entry := [((.node 39, .cont 2), false), ((.dec 3, .node 40), false), ((.inc 3, .cont 2), false), ((.half 1, .node 42), false)]
def entries11 : List Entry := [((.half 3, .inc 5), false), ((.inc 5, .inc 5), false), ((.node 45, .cont 2), false), ((.dec 2, .node 46), false)]
def entries12 : List Entry := [((.inc 2, .cont 2), false), ((.dec 19, .node 48), false), ((.node 49, .brk 1), false), ((.node 47, .node 50), false)]
def entries13 : List Entry := [((.half 3, .node 51), false), ((.dec 19, .node 46), false), ((.node 52, .node 53), false), ((.inc 19, .cont 2), false)]
def entries14 : List Entry := [((.dec 5, .node 55), false), ((.inc 3, .inc 3), false), ((.half 2, .node 57), false), ((.node 58, .brk 2), false)]
def entries15 : List Entry := [((.dec 3, .node 59), false), ((.half 2, .brk 0), false), ((.node 60, .node 61), false), ((.node 56, .node 62), false)]
def entries16 : List Entry := [((.node 54, .node 63), false), ((.node 44, .node 64), false), ((.node 43, .node 65), false), ((.node 15, .node 66), false)]
def entries17 : List Entry := [((.node 10, .brk 1), false), ((.inc 16, .node 68), false), ((.node 3, .node 69), false), ((.node 67, .node 70), false)]
def entries18 : List Entry := [((.node 41, .node 71), false), ((.node 38, .node 72), false), ((.node 36, .node 73), false), ((.node 35, .node 74), false)]
def entries19 : List Entry := [((.node 31, .node 75), false), ((.node 27, .node 76), false), ((.node 77, .cont 2), false), ((.dec 20, .node 78), false)]
def entries20 : List Entry := [((.node 26, .node 79), false), ((.node 24, .node 80), false), ((.node 23, .node 81), false), ((.node 22, .node 82), false)]
def entries21 : List Entry := [((.node 21, .node 83), false), ((.node 19, .node 84), false), ((.node 18, .node 85), false), ((.node 16, .node 86), false)]
def entries22 : List Entry := [((.node 15, .node 87), false), ((.node 14, .node 88), false), ((.node 13, .node 89), false), ((.node 90, .cont 2), false)]
def entries23 : List Entry := [((.dec 18, .node 91), false), ((.inc 7, .inc 4), false), ((.node 93, .cont 2), false), ((.dec 13, .node 94), false)]
def entries24 : List Entry := [((.inc 7, .inc 7), false), ((.node 18, .node 96), false), ((.node 95, .node 97), false), ((.node 98, .cont 2), false)]
def entries25 : List Entry := [((.dec 20, .node 99), false), ((.dec 7, .node 20), false), ((.node 100, .node 101), false), ((.inc 6, .node 102), false)]
def entries26 : List Entry := [((.node 103, .cont 2), false), ((.dec 12, .node 104), false), ((.inc 12, .cont 2), false), ((.dec 6, .node 106), false)]
def entries27 : List Entry := [((.inc 2, .inc 4), false), ((.node 108, .cont 2), false), ((.dec 14, .node 109), false), ((.node 110, .node 8), false)]
def entries28 : List Entry := [((.dec 2, .brk 0), false), ((.node 111, .node 111), false), ((.inc 6, .node 113), false), ((.node 114, .cont 2), false)]
def entries29 : List Entry := [((.dec 15, .node 115), false), ((.dec 6, .node 33), false), ((.dec 11, .node 5), false), ((.inc 11, .cont 2), false)]
def entries30 : List Entry := [((.dec 4, .node 119), false), ((.node 118, .node 120), false), ((.dec 17, .node 37), false), ((.node 3, .brk 1), false)]
def entries31 : List Entry := [((.dec 16, .node 123), false), ((.node 124, .inc 16), false), ((.node 125, .brk 1), false), ((.node 67, .node 126), false)]
def entries32 : List Entry := [((.node 41, .node 127), false), ((.node 122, .node 128), false), ((.node 36, .node 129), false), ((.node 121, .node 130), false)]
def entries33 : List Entry := [((.node 131, .cont 2), false), ((.dec 20, .node 132), false), ((.inc 16, .brk 2), false), ((.dec 16, .node 134), false)]
def entries34 : List Entry := [((.dec 15, .brk 1), false), ((.inc 17, .inc 17), false), ((.node 137, .cont 2), false), ((.dec 14, .node 138), false)]
def entries35 : List Entry := [((.dec 17, .node 7), false), ((.dec 17, .node 33), false), ((.dec 15, .brk 0), false), ((.node 141, .node 142), false)]
def entries36 : List Entry := [((.node 2, .node 143), false), ((.node 9, .node 144), false), ((.inc 13, .node 145), false), ((.node 140, .node 146), false)]
def entries37 : List Entry := [((.node 139, .node 147), false), ((.node 136, .node 148), false), ((.node 135, .node 149), false), ((.node 133, .node 150), false)]
def entries38 : List Entry := [((.node 58, .node 151), false), ((.node 117, .node 152), false), ((.node 116, .node 153), false), ((.node 112, .node 154), false)]
def entries39 : List Entry := [((.node 111, .node 155), false), ((.node 14, .node 156), false), ((.node 15, .node 157), false), ((.node 13, .node 158), false)]
def entries40 : List Entry := [((.node 107, .node 159), false), ((.node 105, .node 160), false), ((.inc 20, .node 161), false), ((.node 19, .node 162), false)]
def entries41 : List Entry := [((.node 92, .node 163), false), ((.node 12, .node 164), false), ((.node 10, .node 165), false), ((.node 9, .node 166), false)]
def entries42 : List Entry := [((.node 3, .node 167), false), ((.node 168, .cont 1), false), ((.inc 12, .brk 1), false), ((.dec 11, .node 170), false)]
def entries43 : List Entry := [((.dec 12, .node 119), false), ((.node 172, .inc 12), false), ((.node 171, .node 173), false), ((.node 169, .node 174), false)]
def entries44 : List Entry := [((.node 2, .node 175), false), ((.inc 14, .node 176), false), ((.node 1, .node 177), false), ((.node 0, .node 178), false)]
def entries45 : List Entry := [((.beep, .node 179), false), ((.node 180, .cont 1), false), ((.inc 12, .node 181), true)]
def entriesFrom46 : List Entry := []
def entriesFrom45 : List Entry := entries45 ++ entriesFrom46
def entriesFrom44 : List Entry := entries44 ++ entriesFrom45
def entriesFrom43 : List Entry := entries43 ++ entriesFrom44
def entriesFrom42 : List Entry := entries42 ++ entriesFrom43
def entriesFrom41 : List Entry := entries41 ++ entriesFrom42
def entriesFrom40 : List Entry := entries40 ++ entriesFrom41
def entriesFrom39 : List Entry := entries39 ++ entriesFrom40
def entriesFrom38 : List Entry := entries38 ++ entriesFrom39
def entriesFrom37 : List Entry := entries37 ++ entriesFrom38
def entriesFrom36 : List Entry := entries36 ++ entriesFrom37
def entriesFrom35 : List Entry := entries35 ++ entriesFrom36
def entriesFrom34 : List Entry := entries34 ++ entriesFrom35
def entriesFrom33 : List Entry := entries33 ++ entriesFrom34
def entriesFrom32 : List Entry := entries32 ++ entriesFrom33
def entriesFrom31 : List Entry := entries31 ++ entriesFrom32
def entriesFrom30 : List Entry := entries30 ++ entriesFrom31
def entriesFrom29 : List Entry := entries29 ++ entriesFrom30
def entriesFrom28 : List Entry := entries28 ++ entriesFrom29
def entriesFrom27 : List Entry := entries27 ++ entriesFrom28
def entriesFrom26 : List Entry := entries26 ++ entriesFrom27
def entriesFrom25 : List Entry := entries25 ++ entriesFrom26
def entriesFrom24 : List Entry := entries24 ++ entriesFrom25
def entriesFrom23 : List Entry := entries23 ++ entriesFrom24
def entriesFrom22 : List Entry := entries22 ++ entriesFrom23
def entriesFrom21 : List Entry := entries21 ++ entriesFrom22
def entriesFrom20 : List Entry := entries20 ++ entriesFrom21
def entriesFrom19 : List Entry := entries19 ++ entriesFrom20
def entriesFrom18 : List Entry := entries18 ++ entriesFrom19
def entriesFrom17 : List Entry := entries17 ++ entriesFrom18
def entriesFrom16 : List Entry := entries16 ++ entriesFrom17
def entriesFrom15 : List Entry := entries15 ++ entriesFrom16
def entriesFrom14 : List Entry := entries14 ++ entriesFrom15
def entriesFrom13 : List Entry := entries13 ++ entriesFrom14
def entriesFrom12 : List Entry := entries12 ++ entriesFrom13
def entriesFrom11 : List Entry := entries11 ++ entriesFrom12
def entriesFrom10 : List Entry := entries10 ++ entriesFrom11
def entriesFrom9 : List Entry := entries9 ++ entriesFrom10
def entriesFrom8 : List Entry := entries8 ++ entriesFrom9
def entriesFrom7 : List Entry := entries7 ++ entriesFrom8
def entriesFrom6 : List Entry := entries6 ++ entriesFrom7
def entriesFrom5 : List Entry := entries5 ++ entriesFrom6
def entriesFrom4 : List Entry := entries4 ++ entriesFrom5
def entriesFrom3 : List Entry := entries3 ++ entriesFrom4
def entriesFrom2 : List Entry := entries2 ++ entriesFrom3
def entriesFrom1 : List Entry := entries1 ++ entriesFrom2
def entriesFrom0 : List Entry := entries0 ++ entriesFrom1
def entries : List Entry := entriesFrom0
def fastNodes : Array Node := #[(.dec 13, .cont 1), (.dec 14, .cont 1), (.dec 15, .cont 1), (.dec 16, .cont 1), (.inc 17, .inc 4), (.node 4, .cont 2), (.dec 14, .node 5), (.inc 14, .cont 2), (.dec 4, .node 7), (.node 6, .node 8), (.dec 18, .cont 1), (.inc 18, .cont 2), (.dec 17, .node 11), (.dec 19, .cont 1), (.dec 2, .cont 1), (.dec 3, .cont 1), (.dec 13, .node 5), (.inc 13, .cont 2), (.dec 4, .node 17), (.dec 20, .cont 1), (.inc 20, .cont 2), (.dec 17, .node 20), (.dec 18, .node 5), (.dec 4, .node 11), (.dec 0, .cont 1), (.inc 0, .cont 2), (.dec 17, .node 25), (.half 0, .inc 3), (.inc 5, .inc 4), (.node 28, .cont 2), (.dec 14, .node 29), (.node 30, .node 8), (.dec 15, .node 29), (.inc 15, .cont 2), (.dec 4, .node 33), (.node 32, .node 34), (.dec 1, .cont 1), (.inc 1, .cont 2), (.dec 5, .node 37), (.half 1, .cont 1), (.node 39, .cont 2), (.dec 3, .node 40), (.inc 3, .cont 2), (.half 1, .node 42), (.half 3, .inc 5), (.inc 5, .inc 5), (.node 45, .cont 2), (.dec 2, .node 46), (.inc 2, .cont 2), (.dec 19, .node 48), (.node 49, .brk 1), (.node 47, .node 50), (.half 3, .node 51), (.dec 19, .node 46), (.node 52, .node 53), (.inc 19, .cont 2), (.dec 5, .node 55), (.inc 3, .inc 3), (.half 2, .node 57), (.node 58, .brk 2), (.dec 3, .node 59), (.half 2, .brk 0), (.node 60, .node 61), (.node 56, .node 62), (.node 54, .node 63), (.node 44, .node 64), (.node 43, .node 65), (.node 15, .node 66), (.node 10, .brk 1), (.inc 16, .node 68), (.node 3, .node 69), (.node 67, .node 70), (.node 41, .node 71), (.node 38, .node 72), (.node 36, .node 73), (.node 35, .node 74), (.node 31, .node 75), (.node 27, .node 76), (.node 77, .cont 2), (.dec 20, .node 78), (.node 26, .node 79), (.node 24, .node 80), (.node 23, .node 81), (.node 22, .node 82), (.node 21, .node 83), (.node 19, .node 84), (.node 18, .node 85), (.node 16, .node 86), (.node 15, .node 87), (.node 14, .node 88), (.node 13, .node 89), (.node 90, .cont 2), (.dec 18, .node 91), (.inc 7, .inc 4), (.node 93, .cont 2), (.dec 13, .node 94), (.inc 7, .inc 7), (.node 18, .node 96), (.node 95, .node 97), (.node 98, .cont 2), (.dec 20, .node 99), (.dec 7, .node 20), (.node 100, .node 101), (.inc 6, .node 102), (.node 103, .cont 2), (.dec 12, .node 104), (.inc 12, .cont 2), (.dec 6, .node 106), (.inc 2, .inc 4), (.node 108, .cont 2), (.dec 14, .node 109), (.node 110, .node 8), (.dec 2, .brk 0), (.node 111, .node 111), (.inc 6, .node 113), (.node 114, .cont 2), (.dec 15, .node 115), (.dec 6, .node 33), (.dec 11, .node 5), (.inc 11, .cont 2), (.dec 4, .node 119), (.node 118, .node 120), (.dec 17, .node 37), (.node 3, .brk 1), (.dec 16, .node 123), (.node 124, .inc 16), (.node 125, .brk 1), (.node 67, .node 126), (.node 41, .node 127), (.node 122, .node 128), (.node 36, .node 129), (.node 121, .node 130), (.node 131, .cont 2), (.dec 20, .node 132), (.inc 16, .brk 2), (.dec 16, .node 134), (.dec 15, .brk 1), (.inc 17, .inc 17), (.node 137, .cont 2), (.dec 14, .node 138), (.dec 17, .node 7), (.dec 17, .node 33), (.dec 15, .brk 0), (.node 141, .node 142), (.node 2, .node 143), (.node 9, .node 144), (.inc 13, .node 145), (.node 140, .node 146), (.node 139, .node 147), (.node 136, .node 148), (.node 135, .node 149), (.node 133, .node 150), (.node 58, .node 151), (.node 117, .node 152), (.node 116, .node 153), (.node 112, .node 154), (.node 111, .node 155), (.node 14, .node 156), (.node 15, .node 157), (.node 13, .node 158), (.node 107, .node 159), (.node 105, .node 160), (.inc 20, .node 161), (.node 19, .node 162), (.node 92, .node 163), (.node 12, .node 164), (.node 10, .node 165), (.node 9, .node 166), (.node 3, .node 167), (.node 168, .cont 1), (.inc 12, .brk 1), (.dec 11, .node 170), (.dec 12, .node 119), (.node 172, .inc 12), (.node 171, .node 173), (.node 169, .node 174), (.node 2, .node 175), (.inc 14, .node 176), (.node 1, .node 177), (.node 0, .node 178), (.beep, .node 179), (.node 180, .cont 1), (.inc 12, .node 181)]
def grammar : Data := ⟨fastNodes, #["$liveframe.0.11", "$liveframe.0.12", "$liveframe.0.8", "$liveframe.0.9", "$scratch.copy", "$micro.a", "$micro.b", "$micro.q", "$micro.r", "$micro.c", "$digit.index", "$liveframe.0.0", "$liveframe.0.1", "$liveframe.0.2", "$liveframe.0.3", "$liveframe.0.4", "$liveframe.0.5", "$pool0.tmp0", "$liveframe.0.6", "$liveframe.0.7", "$liveframe.0.10"], 182⟩
theorem nodes_exact : grammar.nodes = (entries.map Prod.fst).toArray := by rfl

end Shared.PNP.Record285.PreControlGrammar
