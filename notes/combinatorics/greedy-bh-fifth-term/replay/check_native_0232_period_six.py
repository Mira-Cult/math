import ctypes,sys,itertools
Z=ctypes.CDLL('libz3.so.4')
Z.Z3_mk_config.restype=ctypes.c_void_p
Z.Z3_mk_context.argtypes=[ctypes.c_void_p]; Z.Z3_mk_context.restype=ctypes.c_void_p
Z.Z3_del_config.argtypes=[ctypes.c_void_p]
Z.Z3_del_context.argtypes=[ctypes.c_void_p]
Z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p]; Z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
def smt(r,kind,mink):
 a0=((0,0,0,1),(0,1,0,2),(1,1,0,1),(2,0,1,3),(3,0,1,2),(3,1,1,5))[r]
 F=lambda op,*x: '('+' '.join((op,*(str(a) for a in x)))+')'
 ADD=lambda *x:F('+',*x)
 MUL=lambda *x:F('*',*x)
 AND=lambda x:F('and',*x)
 OR=lambda x:F('or',*x)
 SUB=lambda *x:F('-',*x)
 SQ=lambda x,y:F('<=',x,y)
 EQ=lambda x,y:F('=',x,y)
 out=['(set-logic QF_LIA)']
 for v in 'kcqst':out.append(f'(declare-const {v} Int)')
 out.extend([f'(define-fun {n} () Int {ADD(MUL(j,"k"),a)})' for n,j,a in [('h',6,r),('H',6,r+1),('K',3,(r+3)//2),('R',3,r//2),('cB',4,a0[0]),('qB',1,a0[1]),('sB',1,a0[2]),('tB',5 if r%2 else 1,a0[3])]])
 clauses=[SQ(mink,'k'),SQ(ADD('R',1),'c'),SQ('c','h'),SQ(0,'q'),F('<','q','K'),SQ(0,'s'),SQ('s','h'),SQ(0,'t'),SQ('t','h'),F('=>',EQ('s','h'),EQ('t',0)),F('=>',EQ('q',SUB('K',1)),OR([F('<','s',SUB('H','K')),AND([EQ('s',SUB('H','K')),SQ('t','R')])]))]
 pos=[]
 for j,l,z in itertools.product(range(-3,4),range(-4,5),range(-4,5)):
  # All carries allowed; independently derived bounds for h>=60.
  cc=ADD('c',j);b=ADD('q',MUL(-j,'K'),l);a=ADD('s',MUL(j,SUB('K',1)),MUL(-l,'h'),z);d=ADD('t',MUL(-j,'R'),-l,MUL(-z,'H'))
  masks=[tuple(x for i,x in enumerate((a,b,d)) if mask>>i&1) for mask in range(8)]
  pos.append(AND([SQ(ADD(cc,*xs),'h') if xs else SQ(cc,'h') for xs in masks]+[SQ(SUB('x0',*xs),SUB('h',1)) for xs in masks if xs]))
 out.append('(define-fun x0 () Int 0)')
 tuple0='cqst'
 if kind=='improve':
  clauses += [OR([AND([EQ(v,v+'B') for v in tuple0[:i]]+[F('<',a,a+'B')]) for i,a in enumerate(tuple0)]),F('not',OR(pos))]
 elif kind=='collide':
  clauses += [EQ(v,v+'B') for v in tuple0]+[OR(pos)]
 elif kind=='outside':
  clauses=[SQ(mink,'k'),*[EQ(v,v+'B') for v in tuple0],F('not',AND(clauses[1:]))]
 out.extend([f'(assert {x})' for x in clauses]);out.append('(check-sat)')
 return '\n'.join(out)
if __name__ == "__main__":
 for r in range(6):
  for kind in ("outside", "collide", "improve"):
   inp = smt(r,kind,10)
   if "--emit" in sys.argv:
    if str(r) in sys.argv and kind in sys.argv:
     print(inp)
    continue
   cfg = Z.Z3_mk_config()
   ctx = Z.Z3_mk_context(cfg)
   Z.Z3_del_config(cfg)
   ans = Z.Z3_eval_smtlib2_string(ctx,inp.encode()).decode().strip()
   Z.Z3_del_context(ctx)
   assert ans == "unsat", (r,kind,ans)
   print(r,kind,ans,flush=True)
