"""Compilation-relevant reconstruction of Andrew James Wade's TMBuilder.
Source: LegionMammal978/turing_machine_explorer, c3d265ac0555865df8b914ae505cbbea8da75b50.
Comments/debugger omitted; node names simplified (state-graph isomorphism only).
See LICENSE. This file does not claim byte-for-byte upstream reproduction.
"""
import tm
framework='''
#! start 0a.boot1.A
0a.boot1.A 0 1 R 0a.boot1.B
0a.boot1.A 1 1 L 0a.boot1.C
0a.boot1.B 0 0 L 0a.boot1.A
0a.boot1.B 1 0 L 0a.boot1.D
0a.boot1.C 0 1 L 0a.boot1.A
0a.boot1.C 1 1 R [3.register_0.inc]
0a.boot1.D 0 1 L 0a.boot1.B
0a.boot1.D 1 1 R 0a.boot1.E
0a.boot1.E 0 0 R 0a.boot1.D
0a.boot1.E 1 0 R 0a.boot1.B
0b.boot2.0 0 1 L 6.continue.0
0b.boot2.0 1 1 R 0b.boot2.1
0b.boot2.1 0 0 R 0b.boot2.0
0b.boot2.1 1 1 R 0b.boot2.2
0b.boot2.2 0 0 R [3.register_0.inc]
0b.boot2.2 1 1 R [3.register_0.decnz]
1b.reg.prep_1 0 0 R 1b.reg.prep_2
1b.reg.prep_2 0 1 R 1b.reg.prep_2
1b.reg.prep_2 1 1 L 6.continue.0
2b.reg.-1.dec 0 0 R 2b.reg.-2.dec
2b.reg.-1.dec 1 1 R 2b.reg.-1.dec
2b.reg.-1.inc 0 0 R 2b.reg.-2.inc
2b.reg.-1.inc 1 1 R 2b.reg.-1.inc
2b.reg.-2.dec 0 1 L 2c.reg.return_1_1
2b.reg.-2.dec 1 0 R 2b.reg.dec.check
2b.reg.-2.inc 0 1 R 2b.reg.inc.shift_1
2b.reg.-2.inc 1 1 R 2b.reg.-2.inc
2b.reg.dec.check 0 0 L 2b.reg.-2.dec
2b.reg.dec.check 1 1 R 2b.reg.dec.scan_1
2b.reg.dec.scan_1 0 0 R 2b.reg.dec.scan_2
2b.reg.dec.scan_1 1 1 R 2b.reg.dec.scan_1
2b.reg.dec.scan_2 0 0 L 2b.reg.dec.shift_1
2b.reg.dec.scan_2 1 1 R 2b.reg.dec.scan_1
2b.reg.dec.shift_1 0 1 L 2b.reg.dec.shift_2
2b.reg.dec.shift_1 1 1 L 2b.reg.dec.shift_1
2b.reg.dec.shift_2 0 0 L 2c.reg.return_0_1
2b.reg.dec.shift_2 1 0 L 2b.reg.dec.shift_1
2b.reg.inc.shift_1 0 0 L 2c.reg.return_0_1
2b.reg.inc.shift_1 1 0 R 2b.reg.inc.shift_2
2b.reg.inc.shift_2 0 1 R 2b.reg.inc.shift_1
2b.reg.inc.shift_2 1 1 R 2b.reg.inc.shift_2
2c.reg.return_0_1 0 0 L 2c.reg.return_0_2
2c.reg.return_0_1 1 1 L 2c.reg.return_0_1
2c.reg.return_0_2 0 0 L 6.break.0
2c.reg.return_0_2 1 1 L 2c.reg.return_0_1
2c.reg.return_1_1 0 0 L 2c.reg.return_1_2
2c.reg.return_1_1 1 1 L 2c.reg.return_1_1
2c.reg.return_1_2 0 0 L 6.break.1
2c.reg.return_1_2 1 1 L 2c.reg.return_1_1
2e.reg.cleanup_1 0 0 R 2e.reg.cleanup_1
2e.reg.cleanup_1 1 0 R 2e.reg.cleanup_2
2e.reg.cleanup_2 0 0 L 0b.boot2.0
2e.reg.cleanup_2 1 0 R 2e.reg.cleanup_2
4.dispatch.0 0 0 L 4.dispatch.scan
4.dispatch.0 1 1 L 4.dispatch.0
4.dispatch.scan 0 0 R 4.dispatch.scan
4.dispatch.scan 1 1 R 5.root.1
5.root.1 0 0 R 0b.boot2.0
5.root.1 1 1 R 5.root.2
5.root.2 0 0 R main().0
5.root.2 1 0 R main().0
6.break.0 0 1 R 2e.reg.cleanup_1
6.break.0 1 0 L 6.break.0
6.break.1 0 0 L 6.break.0
6.break.1 1 0 L 6.break.1
6.continue.0 0 0 L 6.continue.0
6.continue.0 1 1 L [largest_4.dispatch]
'''
class Register(str):
    @property
    def inc(self): return '3.'+self+'.inc'
    @property
    def dec(self): return '3.'+self+'.dec'
    @property
    def decnz(self): return '3.'+self+'.decnz'
class Sequence:
    def __init__(self,seq):
        self.seq=seq; self.name=None; self.unresolved_labels=set()
def subroutine(func):
    def wrapper(self,*args):
        new_args=tuple(self.add_sequence(v) for v in args)
        key=(func.__name__,*new_args)
        if key in self.memo: return self.memo[key]
        rv=tuple(v for v in (self.add_sequence(v2) for v2 in func(self,*new_args)) if v!=())
        self.memo[key]=rv
        if rv==(): return ()
        i=self.add_sequence(rv)
        if self.sequences[i].name is None:
            self.sequences[i].name='{}({}).0'.format(func.__name__,','.join(str(v) for v in new_args))
        else: self.sequences[i].name='fn_{}().0'.format(i)
        return rv
    return wrapper
class TMBuilder:
    def __init__(self):
        self.tm=tm.TuringMachine(); self.registers={}; self.nextreg=0
        self.sequences=[]; self.sequence_lookup={}; self.memo={}; self.debug=False
    def reg(self,name):
        if name not in self.registers:
            reg=Register(name)
            for op in ('inc','dec'):
                q=f'2b.reg.{self.nextreg}.{op}'
                self.tm.states[q,'0']=tm.Transition('0','R',f'2b.reg.{self.nextreg-1}.{op}')
                self.tm.states[q,'1']=tm.Transition('1','R',q)
            self.tm.states[reg.inc,'0']=tm.Transition('1','R','1b.reg.prep_1')
            self.tm.states[reg.inc,'1']=tm.Transition('0','R',f'2b.reg.{self.nextreg}.inc')
            self.tm.states[reg.decnz,'0']=tm.Transition('1','R','1b.reg.prep_1')
            self.tm.states[reg.decnz,'1']=tm.Transition('0','R',f'2b.reg.{self.nextreg}.dec')
            self.tm.states[reg.dec,'0']=tm.Transition('0','R',reg.decnz)
            self.tm.states[reg.dec,'1']=tm.Transition('0','L','6.break.0')
            self.nextreg+=1; self.registers[name]=reg
        return self.registers[name]
    def add_sequence(self,tree):
        while isinstance(tree,(list,tuple)) and len(tree)==1: tree=tree[0]
        if not isinstance(tree,(list,tuple)): return tree
        if len(tree)==0: return ()
        key=tuple(v for v in (self.add_sequence(entry) for entry in tree) if v!=())
        if len(key)==0: return ()
        if len(key)==1: return key[0]
        if key not in self.sequence_lookup:
            seq=Sequence(key)
            for v in key:
                if isinstance(v,int): seq.unresolved_labels.update(self.sequences[v].unresolved_labels)
                elif v.startswith('break_') or v.startswith('continue_'):
                    seq.unresolved_labels.add(v.split('_',maxsplit=1)[1])
            self.sequence_lookup[key]=len(self.sequences); self.sequences.append(seq)
        return self.sequence_lookup[key]
    def label(self,name,seq,zeros=0,ones=0):
        """Resolve a lexical label through right-associated sequences.

        Extension for this construction: allow references across interned
        subroutines, and normalize singleton / multi-element sequences. The
        emitted control graph is checked against an independent lexical-label
        interpreter; this compiler implementation is not a trusted oracle.
        """
        controls=('break_'+name,'continue_'+name)
        def contains(v):
            if isinstance(v,str):return v in controls
            if isinstance(v,int):return name in self.sequences[v].unresolved_labels
            return any(contains(x) for x in v)
        def resolve(v,z,o):
            if not contains(v):return v
            if isinstance(v,str):
                return f'_break.{z}' if v==controls[0] else f'_continue.{o}'
            if isinstance(v,int):
                return self.add_sequence(resolve(self.sequences[v].seq,z,o))
            xs=[x for x in v if x!=() and x!=[]]
            if len(xs)==1:return resolve(xs[0],z,o)
            if len(xs)>2:xs=[xs[0],tuple(xs[1:])]
            assert len(xs)==2
            return resolve(xs[0],z+1,o),resolve(xs[1],z,o+1)
        return resolve(seq,zeros,ones)
    def find_seq(self,name):
        for i,s in enumerate(self.sequences):
            if s.name==name: return i
        raise KeyError(name)
    def reachable(self):
        grey={self.find_seq('main().0')}; black=set()
        while grey:
            i=grey.pop()
            if i not in black:
                yield i; black.add(i)
                for v in self.sequences[i].seq:
                    if isinstance(v,int): grey.add(v)
    def breakout_common_subsequences(self):
        search_len=max(len(s.seq) for s in self.sequences)
        while search_len>1:
            subsequences=set(); match=None; reachable=list(self.reachable())
            for i in reachable:
                s=self.sequences[i]
                if len(s.seq)>=search_len:
                    for offset in range(len(s.seq)+1-search_len):
                        subseq=s.seq[offset:offset+search_len]
                        if subseq in subsequences: match=subseq; break
                        subsequences.add(subseq)
                if match: break
            if match:
                match_i=self.add_sequence(match)
                for i in reachable:
                    while True:
                        s=self.sequences[i].seq
                        if len(s)>search_len:
                            for offset in range(len(s)+1-search_len):
                                if s[offset:offset+search_len]==match:
                                    self.sequences[i].seq=s[:offset]+(match_i,)+s[offset+search_len:]; break
                            else: break
                        else: break
            else: search_len-=1
    def reduce_to_cons(self):
        i=0
        while i<len(self.sequences):
            s=self.sequences[i].seq
            if len(s)>2: self.sequences[i].seq=(s[0],self.add_sequence(s[1:]))
            i+=1
    def name_sequences(self):
        # Names carry no semantics. Preserve subroutine names and give remaining nodes unique names.
        used=set()
        for i,s in enumerate(self.sequences):
            if s.name is None or s.name in used: s.name=f'node_{i}.0'
            used.add(s.name)
    def generate(self):
        def max_zeros(v):
            if isinstance(v,int):
                s=self.sequences[v].seq
                return max(1+max_zeros(s[0]),max_zeros(s[1]))
            return 0
        def generate_break(level):
            while level>0:
                self.tm.states[f'6.break.{level}','0']=tm.Transition('0','L',f'6.break.{level-1}')
                self.tm.states[f'6.break.{level}','1']=tm.Transition('0','L',f'6.break.{level}')
                level-=1
        def generate_continue(level):
            while level>0:
                self.tm.states[f'6.continue.{level}','0']=tm.Transition('0','L',f'6.continue.{level}')
                self.tm.states[f'6.continue.{level}','1']=tm.Transition('0','L',f'6.continue.{level-1}')
                level-=1
        max_zeros=max(2+max_zeros(self.find_seq('main().0')),2)
        for lineno,l in enumerate(framework.splitlines()): self.tm.loadline(l,'<framework>',lineno)
        for i in range(1,max_zeros+1):
            self.tm.states[f'4.dispatch.{i}','0']=tm.Transition('0','L',f'4.dispatch.{i-1}')
            self.tm.states[f'4.dispatch.{i}','1']=tm.Transition('1','L',f'4.dispatch.{i}')
        self.tm.states['6.continue.0','1']=tm.Transition('1','L',f'4.dispatch.{max_zeros}')
        for reg in self.registers.values():
            if self.tm.states[reg.inc,'1'].nextstate=='2b.reg.0.inc': zero_reg=reg
        self.tm.states['0a.boot1.C','1']=tm.Transition('1','R',zero_reg.inc)
        self.tm.states['0b.boot2.2','0']=tm.Transition('0','R',zero_reg.inc)
        self.tm.states['0b.boot2.2','1']=tm.Transition('1','R',zero_reg.decnz)
        for seq_i in self.reachable():
            seq=self.sequences[seq_i]
            v=seq.seq[0]
            if isinstance(v,int): t=tm.Transition('0','R',self.sequences[v].name)
            elif v.startswith('_break.'):
                if v=='_break.0': t=tm.Transition('1','L','6.continue.0')
                else:
                    k=int(v.split('.')[1])-1; t=tm.Transition('0','L',f'6.break.{k}'); generate_break(k)
            elif v.startswith('_continue.'):
                k=int(v.split('.')[1]); t=tm.Transition('0','L',f'6.continue.{k}'); generate_continue(k)
            else: t=tm.Transition('0','R',v)
            self.tm.states[seq.name,'0']=t
            v=seq.seq[1]
            if isinstance(v,int): t=tm.Transition('1','R',self.sequences[v].name)
            elif v.startswith('_break.'):
                k=int(v.split('.')[1]); t=tm.Transition('0','L',f'6.break.{k}'); generate_break(k)
            elif v.startswith('_continue.'):
                k=int(v.split('.')[1])-1; assert k>=0
                t=tm.Transition('0','L',f'6.continue.{k}'); generate_continue(k)
            else: t=tm.Transition('1','R',v)
            self.tm.states[seq.name,'1']=t
    def build_machine(self):
        self.main(); self.breakout_common_subsequences(); self.reduce_to_cons()
        self.name_sequences(); self.generate(); self.tm.gc(); self.tm.statename=self.tm.start
    @subroutine
    def while_decnz(self,var,body):
        if body==(): return [self.label('loop',[var.decnz,'continue_loop'])]
        return [self.label('loop',[var.decnz,[body,'continue_loop']])]
    @subroutine
    def if_decnz(self,var,body):
        assert body!=(); return [[var.decnz,body]]
    @subroutine
    def if_not_decnz(self,var,body):
        assert body!=(); return [self.label('fn',[[var.decnz,'break_fn'],body])]
    @subroutine
    def pair(self,out,in1,in2):
        assert out not in (in1,in2)
        return [self.label('loop',[self.while_decnz(in1,[in2.inc,out.inc]),
            [in2.decnz,[[out.inc,self.while_decnz(in2,in1.inc)],'continue_loop']]])]
    @subroutine
    def unpair(self,out1,out2,in1):
        assert in1 not in (out1,out2)
        return [self.label('loop',[in1.decnz,[out1.inc,[[out2.decnz,'continue_loop'],
            [self.while_decnz(out1,out2.inc),'continue_loop']]]])]
    @subroutine
    def if_eq(self,in1,in2,body):
        return [self.label('fn',[[self.label('loop',[in1.decnz,[[in2.decnz,'continue_loop'],
            [self.while_decnz(in1,()),'break_fn']]]),
            [in2.decnz,[self.while_decnz(in2,()),'break_fn']]],body])]
    def debug_assert_eq_val(self,var,val):
        assert not self.debug, 'Debug compilation omitted in this reconstruction'
        return []
