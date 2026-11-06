"""Specialize individual proved-zero occurrences before reinterning control."""
from contextlib import contextmanager


@contextmanager
def installed():
    import contextual_tree,abstract_half
    old=contextual_tree.apply
    builders=[]
    def apply(builder):
        first=old(builder)
        before=contextual_tree.grammar(builder)
        summary,replacements,live,data=abstract_half.analyze(builder)
        slots={name:i for i,name in enumerate(before['registers'])}
        selected={}
        for i,((path,operation,_,_),state) in enumerate(zip(data['occurrences'],data['states'])):
            if state is None or not operation.endswith('.decnz'):continue
            register=abstract_half.native_operand(operation) or operation[2:].rsplit('.',1)[0]
            if state[slots[register]]==1:
                selected[path]=dict(index=i,operation=operation,register=register,state=''.join(map(str,state)))
        nodes=[];lookup={};oldnodes=contextual_tree.unpack(before)
        def emit(node,path):
            if type(node) is str:
                if path in selected:return '_break.1'
                return node
            pair=tuple(emit(child,path+str(bit)) for bit,child in enumerate(oldnodes[node]))
            if pair not in lookup:lookup[pair]=len(nodes);nodes.append(pair)
            return lookup[pair]
        root=emit(before['root'],'110')
        contextual_tree.install(builder,nodes,root)
        middle=contextual_tree.grammar(builder)
        cleanup=old(builder)
        after=contextual_tree.grammar(builder)
        builder.zero_context_certificate=dict(format='np-conp-occurrence-zero-specialization-v1',
            input_grammar=before,input_grammar_sha256=contextual_tree.digest(before),
            input_abstract_states=[None if s is None else ''.join(map(str,s)) for s in data['states']],
            input_summary=summary,replacements=selected,
            specialized_grammar=middle,specialized_grammar_sha256=contextual_tree.digest(middle),
            cleanup_certificate=cleanup,output_grammar_sha256=contextual_tree.digest(after),
            relation='only proved-zero DECNZ or HALF occurrences become their unchanged false lexical return; all other occurrences preserved',
            progress='source comparisons terminate; dropped tests have no store/event effect; full grammar core checks exclude jump-only cycles')
        # Keep the original source-to-context certificate intact. The new
        # independently checkable chain follows it in zero-context.json.
        builder.contextual_tree_certificate=first
        builders.append(builder)
        return first
    contextual_tree.apply=apply
    try:yield builders
    finally:contextual_tree.apply=old
