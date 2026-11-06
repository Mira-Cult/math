"""Bypass an INC and its next same-operand DECNZ at that INC entry only."""
from contextlib import contextmanager


@contextmanager
def installed(cleanup):
    import contextual_tree, abstract_half, weak_grammar
    old=contextual_tree.apply
    builders=[]
    def apply(builder):
        first=old(builder)
        before=contextual_tree.grammar(builder)
        _,_,_,data=abstract_half.analyze(builder)
        occurrences=data['occurrences'];edges=data['edges']
        by_path={path:i for i,(path,*_) in enumerate(occurrences)}
        oldnodes=contextual_tree.unpack(before)
        def resolve(path):
            if path.startswith('111'):path='110'
            if len(path)<3:path+='0'*(3-len(path))
            node=before['root'];index=3
            while type(node) is int:
                if index==len(path):path+='0'
                node=oldnodes[node][int(path[index])];index+=1
            if index!=len(path):raise ValueError('extra control path')
            return by_path[path]
        def core(index):
            chain=[]
            while occurrences[index][1].startswith('_'):
                if index in chain:raise ValueError('jump-only cycle')
                chain.append(index);index=edges[index][0][0]
            return index,chain
        def jump(path,kind,skip):
            for index in range(len(path)-1,1 if kind=='_break' else 0,-1):
                if path[index]==('0' if kind=='_break' else '1'):
                    if skip:skip-=1
                    else:return resolve(path[:index]+'1' if kind=='_break' else path[:index+1])
            raise ValueError('escape outside root')
        selected={}
        for i,(path,operation,_,_) in enumerate(occurrences):
            if not operation.endswith('.inc'):continue
            second,between=core(edges[i][0][0])
            if occurrences[second][1]!=operation[:-4]+'.decnz':continue
            target,after=core(edges[second][0][0])
            choices=[]
            for kind in ('_break','_continue'):
                for skip in range(len(path)):
                    try:
                        reached,chain=core(jump(path,kind,skip))
                    except ValueError:continue
                    if reached==target:choices.append((skip,kind,chain))
            if not choices:continue
            skip,kind,chain=min(choices)
            selected[path]=dict(index=i,operation=operation,decrement_index=second,
                decrement_path=occurrences[second][0],decrement=occurrences[second][1],
                between=between,positive_tail=after,target=target,
                replacement=f'{kind}.{skip}',replacement_tail=chain,
                relation='v -> v+1 -> v, positive DECNZ arm for every natural v; no intervening primitive or event')
        nodes=[];lookup={}
        def emit(node,path):
            if type(node) is str:return selected[path]['replacement'] if path in selected else node
            pair=tuple(emit(child,path+str(bit)) for bit,child in enumerate(oldnodes[node]))
            if pair not in lookup:lookup[pair]=len(nodes);nodes.append(pair)
            return lookup[pair]
        root=emit(before['root'],'110');contextual_tree.install(builder,nodes,root)
        middle=contextual_tree.grammar(builder)
        # No jump-only cycle is permitted, even outside the admitted trajectory.
        weak_grammar.core_graph(builder)
        cleanup_certificate=cleanup(builder)
        after=contextual_tree.grammar(builder)
        weak_grammar.core_graph(builder)
        builder.neutral_context_certificate=dict(format='np-conp-occurrence-neutral-excursion-v1',
            input_grammar=before,input_grammar_sha256=contextual_tree.digest(before),
            replacements=selected,specialized_grammar=middle,
            specialized_grammar_sha256=contextual_tree.digest(middle),
            cleanup_certificate=cleanup_certificate,output_grammar_sha256=contextual_tree.digest(after),
            relation='only the INC entry bypasses its same-operand next DECNZ positive arm; other decrement entries remain',
            progress='all intervening paths finite and event-free; all jump-only cycles rejected before and after cleanup')
        builder.contextual_tree_certificate=first;builders.append(builder)
        return first
    contextual_tree.apply=apply
    try:yield builders
    finally:contextual_tree.apply=old
