"""Nonauthor grammar/control review using only frozen JSON artifacts.

This implements its own lexical path interpretation and exact mask transfers.
It imports no producer analyzer, rewriter, compiler or prior context checker.
"""
from copy import deepcopy
from pathlib import Path
import argparse
import hashlib
import json


def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


class Tree:
    def __init__(self,grammar):
        self.g=grammar
        self.registers=grammar['registers'];assert len(set(self.registers))==len(self.registers)
        self.slots={name:i for i,name in enumerate(self.registers)}
        self.nodes=grammar['nodes'];self.root=grammar['root']
        assert type(self.root) is int and 0<=self.root<len(self.nodes)
        for i,pair in enumerate(self.nodes):
            assert type(pair) is list and len(pair)==2
            for child in pair:
                assert type(child) is dict and len(child)==1
                assert set(child)=={'op'} and type(child['op']) is str or set(child)=={'node'} and type(child['node']) is int and 0<=child['node']<i
        self.leaves=[];self.starts={}
        def visit(child,path,ancestors):
            self.starts[path]=len(self.leaves)
            if 'op' in child:self.leaves.append((path,child['op'],ancestors));return
            for bit,descendant in enumerate(self.nodes[child['node']]):
                visit(descendant,path+str(bit),ancestors+[(child['node'],bit)])
        visit({'node':self.root},'110',[])
        self.rows=[]
        for path,op,_ in self.leaves:
            if op.startswith('_break.'):self.rows.append(('jump',self.exit(path,int(op.split('.')[1]))))
            elif op.startswith('_continue.'):self.rows.append(('jump',self.restart(path,int(op.split('.')[1]))))
            elif op.endswith('.decnz'):self.rows.append((op,self.exit(path,0),self.exit(path,1)))
            else:self.rows.append((op,self.exit(path,0)))

    def resolve(self,path):
        if path=='11' or path.startswith('111'):return 0
        return self.starts[path]

    def exit(self,path,skip):
        eligible=[i for i in range(2,len(path)) if path[i]=='0']
        assert type(skip) is int and 0<=skip<len(eligible),'return crosses root'
        at=eligible[-skip-1]
        return self.resolve(path[:at]+'1')

    def restart(self,path,skip):
        eligible=[i for i in range(1,len(path)) if path[i]=='1']
        assert type(skip) is int and 0<=skip<len(eligible),'restart crosses root'
        at=eligible[-skip-1]
        return self.resolve(path[:at+1])

    def core(self):
        retained=[i for i,row in enumerate(self.rows) if row[0]!='jump']
        assert retained,'no retained primitive'
        ids={i:k for k,i in enumerate(retained)}
        max_chain=0
        def onward(index):
            nonlocal max_chain
            seen=set()
            while self.rows[index][0]=='jump':
                assert index not in seen,'administrative-only cycle'
                seen.add(index);index=self.rows[index][1]
            max_chain=max(max_chain,len(seen))
            return ids[index]
        # Every jump is checked, including those outside the entry trajectory.
        for i,row in enumerate(self.rows):
            if row[0]=='jump':onward(i)
        value=dict(entry=onward(0),rows=[[self.rows[i][0],*[onward(j) for j in self.rows[i][1:]]] for i in retained])
        return value,max_chain


def operand(op):
    assert op.startswith('3.')
    name,kind=op[2:].rsplit('.',1);assert kind in ('inc','decnz')
    if name.startswith('$native-half:'):
        assert kind=='decnz';return name[len('$native-half:'):],'half'
    return name,kind


def images(kind,mask):
    """Exact images of the three sets {0}, {1}, and {2,3,...}."""
    result={}
    def add(branch,image):result[branch]=result.get(branch,0)|image
    if kind=='inc':
        if mask&1:add(0,2)
        if mask&6:add(0,4)
    elif kind=='decnz':
        if mask&1:add(1,1)
        if mask&2:add(0,1)
        if mask&4:add(0,6)
    elif kind=='half':
        if mask&1:add(1,1)
        if mask&2:add(0,1)
        if mask&4:add(0,6);add(1,6)
    else:raise AssertionError('unknown operation')
    return result


def closure(tree,words):
    assert len(words)==len(tree.leaves)
    states=[]
    for word in words:
        assert word is None or type(word) is str and len(word)==len(tree.registers) and all(x in '1234567' for x in word)
        states.append(None if word is None else tuple(map(int,word)))
    assert states[0] is not None and all(x&1 for x in states[0]),'all-zero source entry missing'
    live=set();groups={};edges=0;branch_kinds={}
    for index,((path,op,ancestors),state) in enumerate(zip(tree.leaves,states)):
        if state is None:continue
        live.update(ancestors);groups.setdefault(ancestors[-1],[]).append(index)
        if op=='beep' or op.startswith(('_break.','_continue.')):
            successors=[(tree.rows[index][1],state)]
        else:
            name,kind=operand(op);slot=tree.slots[name]
            successors=[]
            for branch,image in images(kind,state[slot]).items():
                updated=list(state);updated[slot]=image
                successors.append((tree.rows[index][branch+1],updated))
                label=kind+':'+str(branch);branch_kinds[label]=branch_kinds.get(label,0)+1
        for target,image in successors:
            admitted=states[target]
            assert admitted is not None and all(not(x&~y) for x,y in zip(image,admitted)),('inductive closure',index,target)
            edges+=1
    return states,live,groups,dict(occurrences=len(states),admitted_occurrences=sum(s is not None for s in states),edges=edges,primitive_branch_images=branch_kinds)


def context(before,after,certificate):
    assert certificate['schema'] in ('horn-contextual-tree-v1','np-conp-native-half-contextual-v1')
    assert certificate['domain']=='all-zero source entry, after the separately verified blank bootstrap'
    assert certificate['event_scope']=='ordered events and retained register operations preserved; primitive and physical times may change'
    assert certificate['input_grammar']==before
    assert certificate['input_grammar_sha256']==digest(before)
    assert certificate['output_grammar_sha256']==digest(after)
    assert before['registers']==after['registers']
    old=Tree(before);Tree(after)
    states,live,groups,report=closure(old,certificate['states_at_occurrences'])
    rows=certificate['zero_rows'];assert type(rows) is list
    zero=set(map(tuple,rows));assert len(zero)==len(rows)
    for key in zero:
        assert key in groups
        op=old.nodes[key[0]][key[1]]['op'];name,kind=operand(op)
        assert kind in ('decnz','half')
        assert all(states[i][old.slots[name]]==1 for i in groups[key]),'excluded read has a nonzero possibility'
    target=certificate['target_nodes'];root=certificate['target_root']
    Tree(dict(registers=before['registers'],nodes=target,root=root))
    mapping=certificate['node_images'];rules=certificate['rewrite_rules']
    assert len(mapping)==len(rules)==len(old.nodes)
    def closed(child,zeros=0,ones=0):
        if 'node' in child:
            pair=target[child['node']]
            return closed(pair[0],zeros+1,ones) and closed(pair[1],zeros,ones+1)
        op=child['op']
        if op.startswith('_break.'):return 0<=int(op.split('.')[1])<=zeros
        if op.startswith('_continue.'):return 0<=int(op.split('.')[1])<=ones
        if op.endswith('.decnz'):return zeros>=1
        return op=='beep' or op.endswith('.inc')
    for i,pair in enumerate(old.nodes):
        children=[{'op':'_break.1'} if (i,bit) in zero else mapping[c['node']] if 'node' in c else c for bit,c in enumerate(pair)]
        left,right=children;image=mapping[i];rule=rules[i]
        if rule=='pair':assert set(image)=={'node'} and target[image['node']]==children
        elif rule=='escape':
            op=left.get('op','')
            assert op.startswith('_break.') and int(op.split('.')[1])>=1
            assert (i,1) not in live and image=={'op':'_break.'+str(int(op.split('.')[1])-1)}
        elif rule=='drop-left-identity':assert left=={'op':'_break.0'} and image==right and closed(right)
        elif rule=='drop-right-identity':assert right=={'op':'_break.0'} and image==left and closed(left)
        else:raise AssertionError('unrecognized rewrite')
    assert mapping[old.root]=={'node':root}
    reached=set();pending=[root]
    while pending:
        index=pending.pop()
        if index in reached:continue
        reached.add(index);pending += [c['node'] for c in target[index] if 'node' in c]
    order=sorted(reached);rename={n:i for i,n in enumerate(order)}
    rebuilt=dict(registers=before['registers'],root=rename[root],nodes=[
        [{'node':rename[c['node']]} if 'node' in c else c for c in target[i]] for i in order])
    assert rebuilt==after,'context rewrite output not reconstructed'
    report.update(zero_rows=len(zero),local_rules=len(rules),nontrivial_rules=sum(r!='pair' for r in rules))
    return report


def specialized(before,replacements):
    nodes=[];interned={}
    def walk(child,path):
        if 'op' in child:return {'op':'_break.1'} if path in replacements else child
        pair=[walk(c,path+str(bit)) for bit,c in enumerate(before['nodes'][child['node']])]
        key=json.dumps(pair,sort_keys=True,separators=(',',':'))
        if key not in interned:interned[key]=len(nodes);nodes.append(pair)
        return {'node':interned[key]}
    root=walk({'node':before['root']},'110')['node']
    return dict(registers=before['registers'],root=root,nodes=nodes)


def zero_chain(first,certificate,output):
    assert certificate['format']=='np-conp-occurrence-zero-specialization-v1'
    before=certificate['input_grammar'];middle=certificate['specialized_grammar']
    assert digest(before)==certificate['input_grammar_sha256']
    assert digest(middle)==certificate['specialized_grammar_sha256']
    assert digest(output)==certificate['output_grammar_sha256']
    first_check=context(first['input_grammar'],before,first)
    tree=Tree(before);states,_,_,invariant=closure(tree,certificate['input_abstract_states'])
    replacements={}
    for index,((path,op,_),state) in enumerate(zip(tree.leaves,states)):
        if state is None or not op.endswith('.decnz'):continue
        register,kind=operand(op);assert kind in ('decnz','half')
        if state[tree.slots[register]]==1:
            replacements[path]=dict(index=index,operation=op,register=register,state=''.join(map(str,state)))
    assert certificate['replacements']==replacements,'wrong zero occurrence inventory'
    assert specialized(before,replacements)==middle,'specialization changes an unselected leaf or return'
    cleanup=context(middle,output,certificate['cleanup_certificate'])
    return dict(original_context=first_check,occurrence_invariant=invariant,
        removed_occurrences=len(replacements),cleanup=cleanup)


def transfer_test():
    # Concrete values exercise both outcomes of the many category. The proof
    # of exactness for all larger values is the arithmetic case split in REVIEW.
    for kind in ('inc','decnz','half'):
        for mask in range(1,8):
            observed={}
            for n in range(64):
                category=1 if n==0 else 2 if n==1 else 4
                if not mask&category:continue
                branch=(int(n%2==0) if kind=='half' else int(n==0) if kind=='decnz' else 0)
                value=(n//2 if kind=='half' else max(n-1,0) if kind=='decnz' else n+1)
                image=1 if value==0 else 2 if value==1 else 4
                observed[branch]=observed.get(branch,0)|image
            assert observed==images(kind,mask)
    return 21


def mutations(first,certificate,output):
    rejected=[]
    def test(name,edit):
        a,b,c=deepcopy(first),deepcopy(certificate),deepcopy(output);edit(a,b,c)
        try:zero_chain(a,b,c)
        except (AssertionError,KeyError,ValueError,IndexError,TypeError):rejected.append(name)
        else:raise AssertionError('accepted mutation: '+name)
    path=next(iter(certificate['replacements']))
    row=certificate['replacements'][path];index=row['index']
    slot=certificate['input_grammar']['registers'].index(row['register'])
    test('input grammar binding',lambda a,b,c:b.update(input_grammar_sha256='0'*64))
    test('missing selected occurrence',lambda a,b,c:b['replacements'].pop(path))
    test('wrong logical operand',lambda a,b,c:b['replacements'][path].update(register='other'))
    def lose_zero(a,b,c):
        word=b['input_abstract_states'][index]
        b['input_abstract_states'][index]=word[:slot]+'2'+word[slot+1:]
    test('zero invariant replaced by positive one',lose_zero)
    def allow_nonzero(a,b,c):
        word=b['input_abstract_states'][index]
        b['input_abstract_states'][index]=word[:slot]+'5'+word[slot+1:]
        b['replacements'][path]['state']=b['input_abstract_states'][index]
    test('selected operand admits nonzero many',allow_nonzero)
    def wrong_branch(a,b,c):
        for pair in b['specialized_grammar']['nodes']:
            for child in pair:
                if child=={'op':'_break.1'}:
                    child['op']='_break.0'
                    b['specialized_grammar_sha256']=digest(b['specialized_grammar']);return
        raise AssertionError('no return')
    test('false branch redirected to success',wrong_branch)
    test('cleanup output binding',lambda a,b,c:b['cleanup_certificate'].update(output_grammar_sha256='0'*64))
    test('source-context predecessor binding',lambda a,b,c:a.update(output_grammar_sha256='0'*64))
    toy=dict(registers=[],root=0,nodes=[[{'op':'_continue.0'},{'op':'beep'}]])
    try:Tree(toy).core()
    except AssertionError:rejected.append('administrative-only cycle')
    else:raise AssertionError('jump-only cycle accepted')
    return rejected


def run(folder):
    folder=Path(folder)
    def read(name):return json.loads((folder/name).read_text())
    first=read('contextual-tree-certificate.json');zero=read('zero-context.json')
    before=read('pre-control-grammar.json');after=read('pre-projection-grammar.json')
    result=zero_chain(first,zero,before)
    a,chain_a=Tree(before).core();b,chain_b=Tree(after).core()
    assert a==b,'ordered primitives or a retained branch changed during finite control rewrites'
    plan=read('weak-grammar-plan.json');cert=read('control-certificate.json')
    graph_sha=hashlib.sha256(json.dumps(a,separators=(',',':')).encode()).hexdigest()
    assert graph_sha==plan['graph_sha256']==cert['core_graph_sha256']
    assert len(a['rows'])==plan['retained_primitives']
    assert cert['contextual_output_grammar_sha256']==digest(before)
    assert cert['finite_control_output_grammar_sha256']==digest(after)
    assert cert['projected_grammar_sha256']==digest(read('pre-coalescence-grammar.json'))
    assert cert['final_grammar_sha256']==digest(read('grammar.json'))
    assert cert['source_sha256']==read('metadata.json')['source_sha256']==plan['source_sha256']
    result.update(format='np-conp-control-independent-occurrence-v1',reviewer='internal-model-reviewer',
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_sha256=cert['source_sha256'],core_sha256=graph_sha,retained_primitives=len(a['rows']),
        maximum_administrative_chain=[chain_a,chain_b],every_administrative_cycle_checked=True,
        exact_mask_transfer_cases=transfer_test(),mutations_rejected=mutations(first,zero,before),
        inputs={name:hashlib.sha256((folder/name).read_bytes()).hexdigest() for name in (
            'contextual-tree-certificate.json','zero-context.json','pre-control-grammar.json',
            'pre-projection-grammar.json','weak-grammar-plan.json','control-certificate.json')},
        scope='all source-entry contexts and admitted primitive branches; exact occurrence rewrites and ordered retained core; no physical timing or bootstrap claim')
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--folder',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();result=run(a.folder);a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2,sort_keys=True))
