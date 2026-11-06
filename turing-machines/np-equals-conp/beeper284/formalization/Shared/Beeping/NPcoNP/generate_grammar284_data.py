from pathlib import Path
import json
p=Path('Shared/Beeping/NPcoNP/Inputs/parent290-grammar.json')
x=json.loads(p.read_text())
assert set(x)=={'nodes','registers','root'}
def q(s):return json.dumps(s,ensure_ascii=True)
def leaf(v):
 assert len(v)==1
 if 'node' in v:return '.node '+str(v['node'])
 assert 'op'in v and all(32<=ord(c)<127 for c in v['op'])
 return '.op '+q(v['op'])
lines=['import Shared.Beeping.NPcoNP.Grammar284Types','','/-! Generated typed grammar AST. The source-byte binding remains', 'an outstanding kernel proof obligation. -/','','namespace Shared.Beeping.NPcoNP.Grammar284','','def producerGrammar : Grammar where','  nodes := #[']
for a,b in x['nodes']:lines.append('    ('+leaf(a)+', '+leaf(b)+'),')
lines[-1]=lines[-1].removesuffix(',')
lines+=['  ]','  registers := #['+', '.join(q(v) for v in x['registers'])+']','  root := '+str(x['root']),'','end Shared.Beeping.NPcoNP.Grammar284','']
Path('Shared/Beeping/NPcoNP/Grammar284Data.lean').write_text('\n'.join(lines))
