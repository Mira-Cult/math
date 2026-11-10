"""Minimal transition-table API, compatible with Wade's compiler.
The compilation-relevant loadline and gc behavior follows upstream tm.py.
"""
from collections import namedtuple
Transition = namedtuple('Transition', 'write direction nextstate')
class TuringMachine:
    def __init__(self):
        self.start = '0'; self.statename = '0'; self.states = {}; self.symbols = set()
    def loadline(self, line, filename='', lineno=0):
        if line.startswith('#! start '): self.start = line.split()[2]
        elif line.strip() and not line.startswith('#'):
            p = line.split()
            assert len(p) == 5, p
            self.states[(p[0],p[1])] = Transition(*p[2:])
            self.symbols.update((p[1],p[2]))
    def gc(self):
        grey={self.start,self.statename}; black=set()
        while grey:
            q=grey.pop()
            if q not in black:
                black.add(q)
                for s in self.symbols:
                    if (q,s) in self.states: grey.add(self.states[q,s].nextstate)
        deleted=[(k,v) for k,v in self.states.items() if k[0] not in black]
        for k,v in deleted: del self.states[k]
        return deleted
    def save(self, path):
        with open(path,'w') as f:
            f.write('#! start '+self.start+'\n')
            for (q,s),t in sorted(self.states.items()):
                f.write(' '.join((q,s,*t))+'\n')
