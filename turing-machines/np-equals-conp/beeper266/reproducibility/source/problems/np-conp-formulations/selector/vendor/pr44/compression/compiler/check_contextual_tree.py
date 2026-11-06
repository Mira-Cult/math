"""No-search checker for zero-test admission and finite local tree rewrites.

Uses the independent tuple-path interpreter for invariant closure, then checks
each supplied rewrite algebraically. It never invokes the producer's analysis,
rewriter, or closed-sequence normalizer.
"""
from pathlib import Path
from functools import lru_cache
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'shared'))
from build_baseline import grammar
from test_occurrences import paths,return_path,continue_path
from test_natural import TreeVM


def check(before,after,certificate):
    if certificate.get('schema')!='horn-contextual-tree-v1':raise ValueError('schema')
    if certificate.get('domain')!='all-zero source entry, after the separately verified blank bootstrap':
        raise ValueError('domain')
    if certificate.get('event_scope')!='ordered events and retained register operations preserved; primitive and physical times may change':
        raise ValueError('event scope')
    def digest(value):
        return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    old=grammar(before);new=grammar(after)
    if old!=certificate.get('input_grammar'):raise ValueError('input grammar')
    if digest(old)!=certificate.get('input_grammar_sha256'):raise ValueError('input grammar digest')
    if digest(new)!=certificate.get('output_grammar_sha256'):raise ValueError('output grammar digest')
    if new['registers']!=old['registers']:raise ValueError('register layout')
    occurrences=list(paths(before));indices={path:i for i,(path,leaf,parent) in enumerate(occurrences)}
    register_indices={str(register):i for i,register in enumerate(before.registers)}
    supplied=certificate.get('states_at_occurrences')
    if type(supplied) is not list or len(supplied)!=len(occurrences):raise ValueError('invariant inventory')
    states=[]
    for state in supplied:
        if state is None:states.append(None)
        elif type(state) is str and len(state)==len(register_indices) and all(c in '1234567' for c in state):
            states.append(tuple(map(int,state)))
        else:raise ValueError('abstract state')
    vm=TreeVM(before)
    def resolve(path):return indices[vm.resolve(path)[1]]
    initial=states[resolve((1,1,0))]
    if initial is None or any(not(x&1) for x in initial):raise ValueError('zero entry missing')
    groups={};live=set();edges=0
    for i,(path,leaf,parent) in enumerate(occurrences):
        state=states[i]
        if state is None:continue
        node=old['root']
        for bit in path[3:]:
            live.add((node,bit));child=old['nodes'][node][bit]
            if 'node' in child:node=child['node']
        # The last descent reaches a leaf, so node remains its canonical
        # parent index even when the supplied builder retains dead sequences.
        groups.setdefault((node,path[-1]),[]).append(i)
        op=str(leaf);successors=[]
        if op.startswith('_break.'):successors.append((return_path(path,int(op.split('.')[1])),state))
        elif op.startswith('_continue.'):successors.append((continue_path(path,int(op.split('.')[1])),state))
        elif op=='beep':successors.append((return_path(path,0),state))
        elif op.startswith('3.'):
            name,kind=op[2:].rsplit('.',1)
            if name not in register_indices or kind not in ('inc','decnz'):raise ValueError('primitive')
            slot=register_indices[name];images={}
            # Both decrement images of >=2 are represented by 2 and 3.
            for value,mask in ((0,1),(1,2),(2,4),(3,4)):
                if not state[slot]&mask:continue
                dest=return_path(path,0 if kind=='inc' else int(value==0))
                value=value+1 if kind=='inc' else max(0,value-1)
                image=1 if value==0 else 2 if value==1 else 4
                images[dest]=images.get(dest,0)|image
            for dest,mask in images.items():
                image=list(state);image[slot]=mask;successors.append((dest,image))
        else:raise ValueError('primitive')
        for destination,image in successors:
            target=states[resolve(destination)]
            if target is None or any(x&~y for x,y in zip(image,target)):
                raise ValueError('invariant not closed at '+str(i))
            edges+=1
    zero_rows=certificate.get('zero_rows')
    if type(zero_rows) is not list or any(type(p) is not list or len(p)!=2 or any(type(x) is not int for x in p) for p in zero_rows):
        raise ValueError('zero-row format')
    zeros={tuple(p) for p in zero_rows}
    if len(zeros)!=len(zero_rows):raise ValueError('duplicate zero row')
    for key in zeros:
        if key not in groups:raise ValueError('zero row without reached invocation')
        child=old['nodes'][key[0]][key[1]]
        op=child.get('op','')
        if not op.endswith('.decnz'):raise ValueError('zero row is not a test')
        slot=register_indices[op[2:].rsplit('.',1)[0]]
        if any(states[i][slot]!=1 for i in groups[key]):raise ValueError('nonzero invocation')

    target=certificate.get('target_nodes');root=certificate.get('target_root')
    if type(target) is not list or type(root) is not int or root not in range(len(target)):
        raise ValueError('target graph')
    def decode(child):
        if type(child) is not dict or len(child)!=1:raise ValueError('child')
        if set(child)=={'node'} and type(child['node']) is int and child['node'] in range(len(target)):
            return child['node']
        if set(child)=={'op'} and type(child['op']) is str:return child['op']
        raise ValueError('child')
    nodes=[]
    for pair in target:
        if type(pair) is not list or len(pair)!=2:raise ValueError('binary target')
        nodes.append(tuple(decode(child) for child in pair))
    # Every constructed node must point backwards: this proves acyclicity
    # even for nodes later discarded because an original right branch is dead.
    if any(type(child) is int and child>=i for i,pair in enumerate(nodes) for child in pair):
        raise ValueError('non-postorder graph')
    maps=certificate.get('node_images');rules=certificate.get('rewrite_rules')
    if type(maps) is not list or type(rules) is not list or len(maps)!=len(old['nodes']) or len(rules)!=len(maps):
        raise ValueError('rewrite inventory')
    maps=[decode(child) for child in maps]
    @lru_cache(None)
    def closed(child,zeros_seen=0,ones_seen=0):
        # Check every lexical escape against its actual internal path, rather
        # than using the producer's bottom-up maximum-demand recurrence.
        if type(child) is int:
            a,b=nodes[child]
            return closed(a,zeros_seen+1,ones_seen) and closed(b,zeros_seen,ones_seen+1)
        if child.startswith('_break.'):
            k=int(child.split('.')[1]);return 0<=k<=zeros_seen
        if child.startswith('_continue.'):
            k=int(child.split('.')[1]);return 0<=k<=ones_seen
        if child.endswith('.decnz'):return zeros_seen>=1
        return child=='beep' or child.endswith('.inc')
    for i,pair in enumerate(old['nodes']):
        children=[]
        for bit,child in enumerate(pair):
            if (i,bit) in zeros:children.append('_break.1')
            elif 'node' in child:children.append(maps[child['node']])
            else:children.append(child['op'])
        left,right=children;result=maps[i];rule=rules[i]
        if rule=='pair':valid=type(result) is int and nodes[result]==tuple(children)
        elif rule=='escape':
            valid=(type(left) is str and left.startswith('_break.') and int(left.split('.')[1])>=1
                   and (i,1) not in live and result=='_break.'+str(int(left.split('.')[1])-1))
        elif rule=='drop-left-identity':valid=left=='_break.0' and result==right and closed(right)
        elif rule=='drop-right-identity':valid=right=='_break.0' and result==left and closed(left)
        else:raise ValueError('rewrite rule')
        if not valid:raise ValueError('invalid rewrite '+str(i))
    if maps[old['root']]!=root:raise ValueError('root image')
    reached=set();todo=[root]
    while todo:
        node=todo.pop()
        if node in reached:continue
        reached.add(node);todo.extend(child for child in nodes[node] if type(child) is int)
    order=sorted(reached);renumber={node:i for i,node in enumerate(order)}
    reconstructed=dict(registers=old['registers'],root=renumber[root],nodes=[
        [{'node':renumber[child]} if type(child) is int else {'op':child} for child in nodes[node]] for node in order])
    if reconstructed!=new:raise ValueError('target grammar binding')
    return dict(abstract_occurrences=len(occurrences),postfixed_edges=edges,
        zero_rows=len(zeros),local_rewrites=len(rules),
        nontrivial_rewrites=sum(rule!='pair' for rule in rules),
        old_nodes=len(old['nodes']),new_nodes=len(new['nodes']),
        scope='zero-entry ordered events and register trace, with changed timing')
