#!/usr/bin/env python3
"""Rebuild the fixed 462481 native context, never a differential proof.

Inputs are authenticated using the existing Raw manifest and canonical source
archive chain. All SQLite connections are read-only. The sole output is the
derived JSON snapshot; --check compares it without changing repository files.
The finite Branch input and high-stem Raw.LogRow literals are checked against
the same input bytes. No parent edges, actual page states or proofs are inferred
from a D/N marker or a recorded final staircase.
"""
from pathlib import Path
import argparse
import csv
import hashlib
import importlib.util
import io
import json
import re
import subprocess
import tempfile
import zipfile

ROOT=Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('contract',ROOT/'KIP126/LinProgram/Translate/native-contract.py')
n=importlib.util.module_from_spec(spec);spec.loader.exec_module(n)
low=n.load_lowstem()
spec=importlib.util.spec_from_file_location('branch_contract',ROOT/'KIP126/LinProgram/Translate/check-branch-d2-coordinates.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
DEFAULT_OUTPUT=ROOT/'KIP126/LinProgram/Generated/Provenance/row462481-trace.json'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='read-only exact snapshot and Lean-input check')
    parser.add_argument('--output',type=Path,default=DEFAULT_OUTPUT)
    parser.add_argument('--archive',type=Path,help='local copy of the SAME fixed cw49 archive')
    args=parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='lin-native-462481-') as tmp:
        report=build_report(args.archive or ROOT/b.ARCHIVE,Path(tmp))
    payload=json.dumps(report,ensure_ascii=False,indent=2)+'\n'
    if args.check:
        require(args.output.read_text()==payload,'derived 462481 snapshot differs; rebuild it from fixed inputs')
    else:
        args.output.write_text(payload)
    print(('Verified' if args.check else 'Wrote')+' fixed 462481 context, both map slices and complete Branch Lean input.')
    print('snapshot sha256='+sha(payload.encode())+'; no actual differential or actual candidate coverage is certified.')


def sha(data): return hashlib.sha256(data).hexdigest()
def require(ok,msg):
    if not ok:raise ValueError(msg)


def build_report(archive,tmp):
    paths={};entities=[]
    for name in ('proofs.db','S0_AdamsSS_t261.db','Ceta_AdamsSS_t200.db','map_AdamsSS_Ceta_to_S0_t200.db','ss.json'):
        path,data,digest=low.pinned(name);paths[name]=path
        entities.append(dict(path='KIP126/LinProgram/Raw/'+name,bytes=len(data),sha256=digest))
        if name=='ss.json':config=json.loads(data)
        del data
    canonical=json.loads((ROOT/'docs/external-inputs.json').read_text())
    source=next(a for a in canonical['sources'] if a['id']=='lwx_machine')
    record_path='Source/LWXMachine/zenodo-record.json'
    record=json.loads((ROOT/record_path).read_text())
    entry=next(f for f in record['files'] if f['key']=='kervaire_database.rar')
    # Reuse the existing checker: record SHA, same-source registered archive
    # identity, complete archive size/MD5, and the member's actual bytes.
    cw_bytes,archive_check=b.checked_archive(ROOT,archive)
    archive_meta=dict(path=b.ARCHIVE,**archive_check,zenodo_record=record_path,
        zenodo_id=record['id'],version=record['metadata']['version'],filename=entry['key'])
    extras=[]
    for name in ('CW_nu_eta_AdamsSS_t200.db','map_AdamsSS_CW_nu_eta_to_Ceta_t200.db'):
        member='kervaire-49/'+name
        extracted=cw_bytes if name.startswith('CW_') else subprocess.check_output(['unrar','p','-inul',str(archive),member])
        path=tmp/name;path.write_bytes(extracted);paths[name]=path
        extras.append(dict(path='KIP126/LinProgram/Raw/'+name,bytes=len(extracted),sha256=sha(extracted),
            member=member,status='authenticated existing archive member; extracted only into a temporary read-only input'))
    log=n.connect(paths['proofs.db']);s=n.connect(paths['S0_AdamsSS_t261.db']);c=n.connect(paths['Ceta_AdamsSS_t200.db']);w=n.connect(paths['CW_nu_eta_AdamsSS_t200.db'])
    m=n.connect(paths['map_AdamsSS_Ceta_to_S0_t200.db']);wm=n.connect(paths['map_AdamsSS_CW_nu_eta_to_Ceta_t200.db'])
    def rows(db,query,args=()):return [dict(r) for r in db.execute(query,args)]
    def basis(db,name,degree):
        return [dict(r,local_index=i) for i,r in enumerate(rows(db,f'SELECT * FROM {name}_AdamsE2_basis WHERE s=? AND t=? ORDER BY id',degree))]
    def slice_(db,name,degree):return dict(spectrum=name,degree=list(degree),basis_dimension=len(basis(db,name,degree)),basis=basis(db,name,degree),
        staircase=rows(db,f'SELECT * FROM {name}_AdamsE2_ss WHERE s=? AND t=? ORDER BY id',degree))
    def xor(*args):
        r=set()
        for a in args:r.symmetric_difference_update(a)
        return sorted(r)
    def apply(cols,v):return xor(*(cols[i] for i in v))
    def vectors(dim):return [[i for i in range(dim) if mask>>i&1] for mask in range(1<<dim)]
    def preimages(cols,target):return [v for v in vectors(len(cols)) if apply(cols,v)==target]
    def relation(db,table,rowid):return rows(db,f'SELECT rowid AS sqlite_rowid,* FROM {table} WHERE rowid=?',(rowid,))[0]
    branch=[n.raw_row(log,i) for i in range(462476,462488)]
    require([(r['reason'],r['depth']) for r in branch]==[('T',1)]*3+[('D',0)]+[('N',0)]*8,'branch structure changed')
    relations={
        'sphere_map_column0':relation(s,'S0_AdamsE2_relations',10210),
        'cw_map_column0_first':relation(c,'Ceta_AdamsE2_relations',13125),
        'cw_map_column0_second':relation(c,'Ceta_AdamsE2_relations',13126),
        'h0_h1':relation(s,'S0_AdamsE2_relations',1),
        'h0_x519':relation(s,'S0_AdamsE2_relations',13637),
        'historical_h3_source':relation(w,'CW_nu_eta_AdamsE2_relations',13675),
        'historical_h3_target':relation(s,'S0_AdamsE2_relations',10936),
    }
    require(relations['sphere_map_column0']['rel']=='24,1,189,1;7,1,279,1','sphere relation changed')
    require(xor(relations['cw_map_column0_first']['rel'].split(';'),relations['cw_map_column0_second']['rel'].split(';'))==['195,1,12','67,1,107,1,0'],'module cancellation changed')
    require(relations['historical_h3_source']['rel']=='3,1,240;438,1,2;0,2,418,1,2','historical source relation changed')
    require(relations['historical_h3_target']['rel']=='3,1,358,1;0,2,437,1','historical target relation changed')
    _,csv_bytes,csv_sha=low.pinned('S0_AdamsE2_relations.csv')
    entities.append(dict(path='KIP126/LinProgram/Raw/S0_AdamsE2_relations.csv',bytes=len(csv_bytes),sha256=csv_sha))
    relation_csv=list(csv.DictReader(io.StringIO(csv_bytes.decode('utf-16'))))
    for key in ('sphere_map_column0','h0_h1','h0_x519','historical_h3_target'):
        r=relations[key]
        matches=[i for i,a in enumerate(relation_csv) if a['rel']==r['rel']]
        require(len(matches)==1,'nonunique CSV match')
        r['csv_ordinal_zero_based']=matches[0]
        r['csv_path']='KIP126/LinProgram/Raw/S0_AdamsE2_relations.csv'
        r['kernel_certification']='existing private relation1 lemma in Certificates/ReplayProducts.lean; no actual CW module comparison' if key=='h0_h1' else dict(
            declaration='KIP126.LinE2.NaturalityHighStemProducts.'+dict(sphere_map_column0='native_map_column0',h0_x519='native_h0_product_zero',historical_h3_target='native_ancestor_product')[key],
            module='KIP126/LinProgram/Certificates/NaturalityHighStemProducts.lean',
            scope='kernel-checked fixed sphere quotient equation only; no actual map, CW module action or differential assertion')
    for key in ('cw_map_column0_first','cw_map_column0_second','historical_h3_source'):
        relations[key]['kernel_certification']='not kernel-certified for this trace'

    def mapdata(db,table,source_db,source_name,source_degrees,target_db,target_name,target_degrees,columns,name):
        slices=[];used={}
        for src,tgt,cols in zip(source_degrees,target_degrees,columns):
            sb=basis(source_db,source_name,src);tb=basis(target_db,target_name,tgt)
            require(len(sb)==len(cols),'matrix shape differs from source dimension')
            raw=[]
            def term(code):
                if target_name=='S0':return (low.mon(code),None)
                values=code.split(',')
                return (low.mon(','.join(values[:-1])),int(values[-1]))
            def polynomial(code):
                result=set()
                if code!='':
                    for value in code.split(';'):result.symmetric_difference_update({term(value)})
                return result
            for row in sb:
                values=list(map(int,row['mon'].split(',')));g=values[-1]
                image=rows(db,f'SELECT * FROM {table} WHERE id=?',(g,))[0]
                generator=rows(source_db,f'SELECT * FROM {source_name}_AdamsE2_generators WHERE id=?',(g,))[0]
                used[g]=dict(generator=generator,image=image)
                coefficient=low.mon(','.join(map(str,values[:-1])))
                substituted={(low.mul(coefficient,a),j) for a,j in polynomial(image['map'])}
                output=set()
                for i in cols[row['local_index']]:output.symmetric_difference_update({term(tb[i]['mon'])})
                if name=='Ceta__S0' and src==(15,140) and row['local_index']==0:
                    witness=polynomial(relations['sphere_map_column0']['rel'])
                elif name=='CW_nu_eta__Ceta' and src==(15,144) and row['local_index']==0:
                    witness=polynomial(relations['cw_map_column0_first']['rel']) ^ polynomial(relations['cw_map_column0_second']['rel'])
                else:witness=set()
                require(substituted ^ output == witness,'map matrix does not match native substitution and displayed relations')
                raw.append(dict(local_index=row['local_index'],coefficient=','.join(map(str,values[:-1])),module_generator=g,stored_generator_image=image['map']))
            slices.append(dict(source=slice_(source_db,source_name,src),target=slice_(target_db,target_name,tgt),
                raw_generator_substitution=raw,columns_after_recorded_relation_reductions=cols,
                matrix_rows=[[int(j in col) for col in cols] for j in range(len(tb))]))
        return dict(native_map=next(a for a in config['maps'] if a['name']==name),
            database_version=rows(db,'SELECT * FROM version ORDER BY id'),used_generators=[used[k] for k in sorted(used)],
            slices=slices,scope='formal module-linear data substitution plus the explicitly listed quotient relations; no actual spectrum map comparison')
    cm=mapdata(m,'map_AdamsE2_Ceta_to_S0',c,'Ceta',[(15,140),(18,142)],s,'S0',[(15,138),(18,140)],
               [[[1],[2],[],[],[]],[[2],[]]],'Ceta__S0')
    cm['selected_vectors']=[dict(side='source',source_coordinates=[1],target_coordinates=[2],source_basis_id=5010,target_basis_id=3002,requires_quotient_reduction=False,raw_all_preimages=preimages([[1],[2],[],[],[]],[2])),
        dict(side='target',source_coordinates=[0],target_coordinates=[2],source_basis_id=5253,target_basis_id=3140,requires_quotient_reduction=False,raw_all_preimages=preimages([[2],[]],[2]))]
    cm['full_matrix_reduction']={'source_column':0,'raw_image':'24,1,189,1','target_basis_monomial':'7,1,279,1','target_local_index':1,'relation':'sphere_map_column0','kernel_certified':True,'scope':'fixed sphere quotient equation only; actual top-cell comparison is unproved'}
    cm['native_source_staircase_reciprocal']={'outgoing':rows(c,'SELECT * FROM Ceta_AdamsE2_ss WHERE id=5012')[0], 'incoming':rows(c,'SELECT * FROM Ceta_AdamsE2_ss WHERE id=5254')[0]}
    cwm=mapdata(wm,'map_AdamsE2_CW_nu_eta_to_Ceta',w,'CW_nu_eta',[(15,144),(18,146)],c,'Ceta',[(15,140),(18,142)],
               [[[3],[1]],[[0],[1],[],[]]],'CW_nu_eta__Ceta')
    cwm['selected_vectors']=[dict(side='source',source_coordinates=[1],target_coordinates=[1],source_basis_id=5443,target_basis_id=5010,requires_quotient_reduction=False,raw_all_preimages=preimages([[3],[1]],[1])),
        dict(side='target',source_coordinates=[0],target_coordinates=[0],source_basis_id=5720,target_basis_id=5253,requires_quotient_reduction=False,raw_all_preimages=preimages([[0],[1],[],[]],[0]))]
    cwm['full_matrix_reduction']={'source_column':0,'raw_image':'195,1,12','target_basis_monomial':'67,1,107,1,0','target_local_index':3,
        'relations':['cw_map_column0_first','cw_map_column0_second'],'operation':'XOR of the two displayed module relations','kernel_certified':False}
    # The d2 quotient, independently of the later D label.
    incoming=basis(w,'CW_nu_eta',(16,145));candidate_basis=basis(w,'CW_nu_eta',(18,146))
    incols=[n.coordinates(r['d2']) for r in incoming];outcols=[n.coordinates(r['d2']) for r in candidate_basis]
    require(incols==[[1,3],[],[],[],[]] and outcols==[[],[2],[],[2]],'native d2 matrices changed')
    cycles=[v for v in vectors(4) if not apply(outcols,v)]
    boundaries=sorted({tuple(apply(incols,v)) for v in vectors(5)})
    representatives=[[],[0],[2],[0,2]]
    normalforms=[]
    for z in cycles:
        pairs=[(r,list(b)) for r in representatives for b in boundaries if xor(r,b)==z]
        require(len(pairs)==1,'candidate quotient normal form not unique')
        normalforms.append(dict(cycle=z,representative=pairs[0][0],boundary=pairs[0][1]))
    nonboundary=[]
    for degree,prior,witness in [((19,147),(17,146),[1]),((19,148),(17,147),[5])]:
        bs=basis(w,'CW_nu_eta',prior);cols=[n.coordinates(r['d2']) for r in bs]
        span=sorted({tuple(apply(cols,v)) for v in vectors(len(cols))})
        require(tuple(witness) not in span,'diagnostic vector lies in native d2 boundary image')
        nonboundary.append(dict(degree=list(degree),incoming=slice_(w,'CW_nu_eta',prior),d2_columns=cols,
            image=[list(b) for b in span],claimed_nonboundary=witness,target=slice_(w,'CW_nu_eta',degree),
            status='finite raw matrix nonmembership checked in Python; actual B2 comparison is unproved'))
    source_archive='Source/LWXMachine/source-code.zip'
    source_artifact=next(a for a in source['artifacts'] if a['path']==source_archive)
    source_bytes=(ROOT/source_archive).read_bytes()
    require(sha(source_bytes)==source_artifact['sha256'] and len(source_bytes)==source_artifact['size'],'canonical source archive mismatch')
    source_zip=zipfile.ZipFile(io.BytesIO(source_bytes))
    program=[]
    for file,locators in [('ss/mylog.h',['EnumReason and REASONS_DB lines 13-40']),('ss/mylog.cpp',['InsertDiff lines 37-47','LogDiff lines 150-179']),('ss/deduce.cpp',['TryDiff lines 331-386','DeduceDiff4Nd lines 405-445 and 489-504, including nd.count==0 direct-zero branch']),('ss/category.cpp',['MapMod2Ring::map lines 182-195','SetModuleDiffGlobal lines 407-451'])]:
        raw=source_zip.read('SSeqCpp-master/'+file)
        program.append(dict(member='SSeqCpp-master/'+file,sha256=sha(raw),locators=locators))
    queries=dict(branch='SELECT * FROM log WHERE id BETWEEN 462476 AND 462487 ORDER BY id',
        predecessor='SELECT * FROM log WHERE id BETWEEN 462473 AND 462475 ORDER BY id',
        next_branch_start='SELECT * FROM log WHERE id=462488',
        prior_exact_state='SELECT * FROM log WHERE id<462476 AND depth=0 AND name=\'CW_nu_eta\' AND s=16 AND t=145 ORDER BY id',
        prior_exact_source='SELECT * FROM log WHERE id<462476 AND depth=0 AND name=\'CW_nu_eta\' AND s=16 AND t=145 AND x=\'3\' ORDER BY id')
    report=dict(schema='lin-native-row462481-trace-context/v1',status='fixed-native-data-and-local-branch-context-only; not-a-differential-proof',
        provenance=dict(canonical_manifest='docs/external-inputs.json',raw_manifest='KIP126/LinProgram/Raw/manifest.json',
            pinned_inputs=entities,existing_data_archive=archive_meta,additional_existing_archived_inputs=extras,
            program_source_archive=dict(path=source_archive,sha256=sha((ROOT/source_archive).read_bytes()),members=program)),
        target=n.raw_row(log,462481),adjacent_context=dict(previous_branch=rows(log,queries['predecessor']),branch_rows=branch,next_branch_start=n.raw_row(log,462488),
            interpretation='The 3 T rows are failed-trial records with full diagnostics; 462479 is the retained program claim. 462480-462487 record propagation. This database has only the log table and no parent-edge or exclusions table.'),
        trace_edges=[dict(source_id=462479,target_id=462480,map='CW_nu_eta__Ceta',shift=4,source_degrees=[[15,144],[18,146]],target_degrees=[[15,140],[18,142]],
            status='reconstructed from adjacent native payloads, map metadata and selected data images; no explicit parent-id column'),
            dict(source_id=462480,target_id=462481,map='Ceta__S0',shift=2,source_degrees=[[15,140],[18,142]],target_degrees=[[15,138],[18,140]],
            status='reconstructed from adjacent native payloads, map metadata and selected data images; no explicit parent-id column')],
        maps=dict(cw_to_ceta=cwm,ceta_to_sphere=cm),relations=relations,
        candidate_coverage=dict(degree=[18,146],source_slice=slice_(w,'CW_nu_eta',(15,144)),
            source_incoming_d2=slice_(w,'CW_nu_eta',(13,143)),incoming=slice_(w,'CW_nu_eta',(16,145)),
            target=slice_(w,'CW_nu_eta',(18,146)),outgoing_target=slice_(w,'CW_nu_eta',(20,147)),
            dimensions=[5,4,4],incoming_d2_columns=incols,outgoing_d2_columns=outcols,
            incoming_matrix_rows=[[int(j in col) for col in incols] for j in range(4)],
            outgoing_matrix_rows=[[int(j in col) for col in outcols] for j in range(4)],
            cycle_vectors=cycles,boundary_vectors=[list(b) for b in boundaries],quotient_representatives=representatives,
            unique_raw_normal_forms=normalforms,excluded_trial_vectors=[[],[2],[0,2]],retained_vector=[0],
            status='raw finite quotient enumeration verified in Python; no actual E3 spanning or independence theorem',
            necessary_mathematical_statement='Every actual E3 target at (18,146) is represented by exactly one of [], [0], [2], [0,2] through the same CW_nu_eta interpretation; its d2 kernel and boundary image must agree with the displayed matrices. The D tag does not imply this statement.'),
        diagnostic_state_dependencies=dict(h0=slice_(s,'S0',(1,1)),h1=slice_(s,'S0',(1,2)),
            previously_supported_differential=dict(spectrum='CW_nu_eta',page=3,source=dict(degree=[16,145],coordinates=[3]),target=dict(degree=[19,147],coordinates=[1]),
                final_native_source_staircase=rows(w,'SELECT * FROM CW_nu_eta_AdamsE2_ss WHERE id=5603')[0],
                final_native_target_staircase=rows(w,'SELECT * FROM CW_nu_eta_AdamsE2_ss WHERE id=5859')[0],
                prior_root_logs_in_source_degree=rows(log,queries['prior_exact_state']),prior_root_logs_with_exact_source=rows(log,queries['prior_exact_source']),
                status='explicit prerequisite already used by earlier T462354/462355. The independent algebraic reconstruction below identifies sufficient prior native claims, not primitive parent edges or actual proofs. Final staircase rows are not proof inputs.',
                earlier_presupposition_context=[n.raw_row(log,i) for i in range(462353,462357)],
                independent_algebraic_reconstruction=historical_reconstruction(log,s,w,relations,slice_)),
            nonboundary_checks=nonboundary,
            product_identities=[
                dict(multiplier='S0(1,1)[0]',input='CW_nu_eta(15,144)[1]',output='CW_nu_eta(16,145)[3]',method='direct native monomial match'),
                dict(multiplier='S0(1,1)[0]',input='CW_nu_eta(18,146)[2]',output='zero',method='sphere relation h0_x519 times module generator0',sphere_quotient_lemma='KIP126.LinE2.NaturalityHighStemProducts.native_h0_product_zero',kernel_certified=False),
                dict(multiplier='S0(1,2)[0]',input='CW_nu_eta(15,144)[1]',output='zero',method='sphere relation h0_h1 times generator418 and module generator2; actual module comparison unproved'),
                dict(multiplier='S0(1,2)[0]',input='CW_nu_eta(18,146)[0,2]',output='CW_nu_eta(19,148)[5]',method='h0_h1 kills the coordinate0 term; coordinate2 term directly matches basis6015',kernel_certified=False)]),
        source_semantics=dict(T='EnumReason.try1: a hypothesized target tested in a temporary node; successful trials are rolled back from the log; the retained diagnostic is a program failure, not a Lean contradiction proof',
            D='EnumReason.deduce has a direct zero-target branch when nd.count==0, and an enumerated-candidate branch when exactly one trial survives. For nonzero output462479 the latter explains the marker. Neither case proves actual candidate coverage or trial soundness.',
            N='EnumReason.nat: after native generator substitution and target Groebner reduction, the program logs the claimed image differential. It does not construct a morphism of actual Adams sequences.',
            nulls='JSON null retains SQL NULL. In particular info=NULL at 462479 is absent information, and diff=NULL in the displayed staircase rows is not an empty differential vector.',
            zero='The empty string in x/dx/d2 or a stored generator map encodes the explicit zero vector/polynomial; string "0" is coordinate [0], never zero.'),
        reuse_plan=dict(generic_naturality='KIP126.Classical.Adams.adamsInternalE2Induced_hasDifferential',
            same_route_top_cell='KIP126.Interface.Solution.LinProgram.Naturality.topCell',
            generic_double_desuspension='KIP126.Classical.Adams.Suspension.TowerComparison.hasDifferential_desuspendTwice',
            fixed_double_desuspension='KIP126.Interface.Solution.LinProgram.Naturality.doubleDesuspensionCompatible',
            exact_source_premise='HasDifferential cetaSequence 3 (15,140) (18,142) (coordinates 15 140 1) (coordinates 18 142 0)',
            intermediate_degrees=[[15,139],[18,141]],final_degrees=[[15,138],[18,140]],
            coordinate_comparisons='The same actual topCell and the same two standardRouteModel.classicalSuspension comparisons must send the selected Ceta labels to P.comparison of native S0 basis3002/[2] and basis3140/[2].',
            restriction='The existing row245130_topCell and row245131 wrappers are specialized to their own low-degree labels; reuse the generic laws or add a correctly specialized wrapper. Do not reuse a D-only log parser for the N source462480.'),
        remaining_propositions=[
            'Prove the exact actual Ceta source differential at (15,140)[1] -> (18,142)[0], without using the target sphere differential or total computation delivery.',
            'If replaying the local ancestor branch, construct the actual CW_nu_eta object and shift-four map to the same Ceta; compare the displayed source and target images.',
            'Prove actual E3 candidate coverage and the three trial exclusions using the same CW_nu_eta model, genuine page/module Leibniz, multiplier cycles and actual earlier-boundary nonmembership.',
            'For the historical state, prove actual D461961: CW_nu_eta d3(15,137)[0]=(18,139)[0], actual D153861: S0 d3(15,138)[0]=0, and d3-cycles for S0(1,8)[0] and CW_nu_eta(1,7)[0]; then use actual module Leibniz and the historical_h3_source/target coordinate comparisons to add source[2,3]+[2]=[3] and target[1]+0=[1]. These are sufficient reconstructed dependencies, not recorded parent edges.',
            'Certify the Ceta module reduction at rowids13125+13126 and the historical CW module reduction at rowid13675. Sphere quotient reductions at rowids10210,13637,10936 are kernel-certified separately; actual module and map comparisons remain unproved. Selected map vectors themselves require no quotient reduction.',
            'Compare both selected Ceta-to-S0 images with the actual topCell and the same two proved tower desuspensions, preserving the existing literature/bindings/model.'
        ],queries=queries)
    b.check_contract(b.read_slices(w),report,(ROOT/b.LEAN).read_text())
    check_raw_naturality(n.raw_row(log,462479),n.raw_row(log,462480),n.raw_row(log,462481))
    for db in (log,s,c,w,m,wm):db.close()
    return report


def historical_reconstruction(log,s,w,relations,slice_):
    cw=n.raw_row(log,461961);sphere=n.raw_row(log,153861)
    require(n.equation(cw)==dict(spectrum='CW_nu_eta',page=3,
        source=dict(degree=[15,137],coordinates=[0]),target=dict(degree=[18,139],coordinates=[0])),
        'historical CW claim changed')
    require(n.equation(sphere)==dict(spectrum='S0',page=3,
        source=dict(degree=[15,138],coordinates=[0]),target=dict(degree=[18,140],coordinates=[])),
        'historical sphere claim changed')
    for row in (cw,sphere):
        require(row['depth']==0 and row['reason']=='D' and row['info'] is None,
                'historical native claim payload changed')
    cw_source=slice_(w,'CW_nu_eta',(15,137))
    cw_target=slice_(w,'CW_nu_eta',(18,139))
    sphere_source=slice_(s,'S0',(15,138))
    sphere_target=slice_(s,'S0',(18,140))
    h3=slice_(s,'S0',(1,8))
    module_multiplier=slice_(w,'CW_nu_eta',(1,7))
    dest_source=slice_(w,'CW_nu_eta',(16,145))
    dest_target=slice_(w,'CW_nu_eta',(19,147))
    def module_mon(code):
        nums=code.split(',')
        return (low.mon(','.join(nums[:-1])),int(nums[-1]))
    def product(ring_code,module_code):
        coefficient,gen=module_mon(module_code)
        return (low.mul(low.mon(ring_code),coefficient),gen)
    def mon(slice_,index):return slice_['basis'][index]['mon']
    def module_vector(slice_,indices):return {module_mon(mon(slice_,i)) for i in indices}
    source_product={product(mon(h3,0),mon(cw_source,0))}
    source_normal=module_vector(dest_source,[2,3])
    source_relation={module_mon(term) for term in relations['historical_h3_source']['rel'].split(';')}
    require(source_product ^ source_normal == source_relation,'historical source relation witness failed')
    target_product={product(mon(h3,0),mon(cw_target,0))}
    target_normal=module_vector(dest_target,[1])
    target_relation={(low.mon(term),2) for term in relations['historical_h3_target']['rel'].split(';')}
    require(target_product ^ target_normal == target_relation,'historical target relation witness failed')
    require({product(mon(sphere_source,0),mon(module_multiplier,0))}==module_vector(dest_source,[2]),
            'historical direct source product mismatch')
    require([r['id'] for r in h3['basis']]==[15] and
            [r['id'] for r in module_multiplier['basis']]==[11], 'historical multipliers changed')
    return dict(
        status='independent algebraic reconstruction from two earlier native claims; not logged parent edges, not actual differentials',
        terms=[dict(seed_log=cw,multiplier=h3,multiplier_selected_index=0,
            seed_source=cw_source,seed_target=cw_target,
            source_product=[2,3],target_product=[1],
            source_relation='historical_h3_source',target_relation='historical_h3_target',
            sphere_quotient_lemma='KIP126.LinE2.NaturalityHighStemProducts.native_ancestor_product',
            required_actual_cycle='S0 d3(1,8)[0]=0',kernel_certified=False),
            dict(seed_log=sphere,multiplier=module_multiplier,multiplier_selected_index=0,
            seed_source=sphere_source,seed_target=sphere_target,
            source_product=[2],target_product=[],source_relation=None,target_relation=None,
            required_actual_cycle='CW_nu_eta d3(1,7)[0]=0',kernel_certified=False)],
        source_sum=dict(degree=[16,145],summands=[[2,3],[2]],coordinates=[3]),
        target_sum=dict(degree=[19,147],summands=[[1],[]],coordinates=[1]),
        checked_algebra='The two source/target polynomial differences equal the displayed native relations; the second source product matches a basis monomial directly. Coordinate addition is XOR. These checks do not supply the actual module comparison.',
        ancestor_context=[
            dict(seed_id=461961,previous=n.raw_row(log,461957),
                 branch=[n.raw_row(log,i) for i in range(461958,461969)],next=n.raw_row(log,461969)),
            dict(seed_id=153861,previous=n.raw_row(log,153853),
                 branch=[n.raw_row(log,i) for i in range(153854,153862)],next=n.raw_row(log,153862))],
        required_mathematical_inputs=[
            'Actual interpretations of the two earlier D statements on the same sphere and CW_nu_eta objects; their retained D markers and adjacent failed trials do not prove them.',
            'Actual d3-cycle statements for both selected low-degree multipliers; native final staircase diff=NULL is not a proved zero differential.',
            'Actual module Leibniz, bilinearity and the displayed relation-to-coordinate comparisons, all on the same objects.',
            'Soundness and completeness of each earlier branch if those D statements are themselves replayed; this reconstruction does not recursively certify their trial diagnostics.'
        ])


def check_raw_naturality(cw,source,target):
    path=ROOT/'KIP126/LinProgram/Raw/NaturalityHighStem.lean'
    n.check_raw_high_stem_declarations(path.read_text(),cw,source,target)


if __name__=='__main__':
    main()
