"""Exact blank bootstrap, two literal simulators, source and primitive checks."""
from pathlib import Path
import json,argparse,subprocess,tempfile,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
import integrated_build
from check_contextual_quotient import check as check_contextual
from machine import emit,parse,simulate
from test_natural import TreeVM,SourceVM,AuditLimit
from test_machine import decode_registers
from test_occurrences import check as check_occurrences

def verify(source,table,events=3,literal_limit=3_000_000_000,*,horner=False,second_simulator='python'):
    if second_simulator not in ('python','bitset'):raise ValueError('second simulator')
    source,table=Path(source),Path(table)
    b,raw,final,names,mapping,_,maximum=integrated_build.construct(source,horner=horner)
    parsed=parse(table)
    assert (parsed.start,parsed.beep,parsed.rows)==(final.start,final.beep,final.rows)
    replay=check_contextual(b,raw,final,names,b.contextual_certificate)
    main=names['main().0'];mapped_main=mapping[main]
    with tempfile.TemporaryDirectory(prefix='horn-compression-physical-') as tmp:
        tmp=Path(tmp);emit(raw,tmp/'raw.tm');emit(final,tmp/'selected.tm')
        assert (tmp/'selected.tm').read_bytes()==table.read_bytes()
        executable=tmp/'simulator'
        subprocess.run(['g++','-std=c++17','-O2',str(ROOT/'shared/simulate.cpp'),'-o',str(executable)],check=True)
        independent=tmp/'bitset'
        if second_simulator=='bitset':
            subprocess.run(['gcc','-std=c11','-O2','-Wall','-Wextra','-Werror',str(HERE/'literal_bitset.c'),'-o',str(independent)],check=True)
        def literal(path,limit,beeps=0,stop=-1,exe=executable):
            return json.loads(subprocess.check_output([str(exe),str(path),str(limit),str(beeps),str(stop)],text=True))
        boot=literal(tmp/'raw.tm',literal_limit,stop=main)
        assert boot['state']==main and boot['head']==-3818 and boot['beeps']==[]
        assert boot['ones']==[-3821,-3820]+list(range(3,3822,2))
        if second_simulator=='python':
            assert simulate(raw,boot['steps']+1,stop_state=main)==boot
        else:
            assert literal(tmp/'raw.tm',boot['steps']+1,stop=main,exe=independent)==boot
        mapped_boot=literal(table,boot['steps'])
        assert mapped_boot['state']==mapped_main
        assert all(mapped_boot[k]==boot[k] for k in ('steps','head','ones','beeps'))
        vm=TreeVM(b);vm.until_beeps(events)
        oracle=SourceVM(source.read_text(),beep_limit=events)
        try:oracle.call('main',())
        except AuditLimit as error:assert error.args[0]==('beep limit reached',events)
        else:raise AssertionError('complete controller returned')
        current=(mapped_main,boot['head'],boot['ones']);elapsed=boot['steps']
        times=[];observations=[]
        for number,(_,registers) in enumerate(vm.beep_records,1):
            observed=literal(table,literal_limit,beeps=number)
            if len(observed['beeps'])!=number:
                raise RuntimeError(f'literal budget {literal_limit} exhausted before event {number}')
            delta=observed['steps']-elapsed
            if second_simulator=='python':
                checked=simulate(parsed,delta+1,initial=current,stop_after_beeps=1)
                assert checked['steps']==delta and checked['beeps']==[delta]
                assert all(checked[k]==observed[k] for k in ('state','head','ones'))
            else:
                checked=literal(table,literal_limit,beeps=number,exe=independent)
                assert checked==observed
            physical=decode_registers(checked['ones'],3,b.registers)
            assert all(physical[name]==registers.get(name,0) for name in b.registers)
            active={name:value for name,value in oracle.beeps[number-1].items()
                    if name in ('main.k','main.program')}
            assert all(physical[b.logical_to_physical.get(name,name)]==value for name,value in active.items())
            elapsed+=delta;times.append(elapsed);observations.append(active)
            current=(checked['state'],checked['head'],checked['ones'])
        assert times==observed['beeps']
    return dict(status='passed',
        source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        table_sha256=hashlib.sha256(table.read_bytes()).hexdigest(),
        states=parsed.count,transitions=len(parsed.rows),raw_states=raw.count,
        registers=len(b.registers),max_leaf_path=maximum,
        bootstrap_transitions=boot['steps'],bootstrap_head=boot['head'],bootstrap_ones=len(boot['ones']),
        beep_times=times,source_main_observations=observations,
        primitive_beep_steps=[step for step,_ in vm.beep_records],
        all_occurrences=check_occurrences(b),contextual_certificate_replay=replay,
        quotient_rows_checked=replay['physical_rows_checked'],ignored_rows=replay['ignored_rows'],
        audit_literal_limit=literal_limit,
        horner_fusion=horner,
        literal_simulators=['shared/simulate.cpp',
            'shared/machine.py' if second_simulator=='python' else 'compression/literal_bitset.c'],
        literal_simulator_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
            for name in ('shared/simulate.cpp',
                'shared/machine.py' if second_simulator=='python' else 'compression/literal_bitset.c')},
        verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_observation_contract='candidate k/program at events; all physical registers and whole tape also equal TreeVM',
        scope='finite blank-run regression; conditional contextual quotient and unbounded source/runtime proofs are separate')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=HERE/'source/source.py')
    p.add_argument('--table',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--events',type=int,default=3);p.add_argument('--literal-limit',type=int,default=3_000_000_000)
    p.add_argument('--horner',action='store_true')
    p.add_argument('--second-simulator',choices=('python','bitset'),default='python');a=p.parse_args()
    if a.out.exists():raise ValueError('evidence output must be fresh')
    result=verify(a.source,a.table,a.events,a.literal_limit,horner=a.horner,second_simulator=a.second_simulator)
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))
