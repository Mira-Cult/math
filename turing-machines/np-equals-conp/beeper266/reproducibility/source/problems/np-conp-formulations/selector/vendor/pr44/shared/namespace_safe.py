"""Separate copy scratch from every possible source procedure/variable name."""
from assigned_natural import AssignedNaturalBuilder
import tm


class NamespaceSafeBuilder(AssignedNaturalBuilder):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        # Construction has only installed the inherited shared copy scratch.
        # Rebuild that one initial register under an impossible Python name.
        assert list(self.registers)==['scratch.copy'] and not self.sequences
        self.tm=tm.TuringMachine()
        self.registers={}
        self.nextreg=0
        self.scratch=self.reg('$scratch.copy')

    def temporary_prefix(self,frame):
        if self.pooled_temporaries:
            return f"$pool{self.heights[frame['name']]}.tmp"
        return f"$temporary.{frame['name']}.tmp"

    def alloc(self,frame):
        index=0
        while index in frame['used']:
            index+=1
        frame['used'].add(index)
        return self.reg(self.temporary_prefix(frame)+str(index))

    def free(self,frame,register):
        prefix=self.temporary_prefix(frame)
        assert str(register).startswith(prefix)
        frame['used'].remove(int(str(register)[len(prefix):]))
