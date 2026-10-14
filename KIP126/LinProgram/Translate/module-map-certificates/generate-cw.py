#!/usr/bin/env python3
"""Full CW→Ceta native relation certificate plan, using the existing checker.
Generated math evaluates in the original full target module over original E2.
Auxiliary witnesses are checked against authenticated source entities, never
accepted as mathematical axioms or as certified program traces.
"""
import argparse, hashlib, importlib.util, json, pathlib, re

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent.parent))
from lean_module import lean_module, module_output
BASE='KIP126.LinProgram.Certificates.ModuleMaps'
NS='KIP126.LinModule.NativeMapCertificates'
CW='KIP126.LinModule.CWToCeta'
HEADER=f'''open NamedElementCertificates
open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open KIP126.LinE2.NativeModuleCertificates.Support
open {NS}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local cbv_eval] SquareDetection.splitOn_comma
  SquareDetection.splitOn_semicolon SquareDetection.toNat?_eq_chars
'''
def require(c,m):
 if not c:raise ValueError(m)
def canonical(x):return (json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':'))+'\n').encode()
def sha(b):return hashlib.sha256(b).hexdigest()
def lit(x):return json.dumps(x,ensure_ascii=False,separators=(', ',': '))
def load(root,name,file):
 spec=importlib.util.spec_from_file_location(name,root/'KIP126/LinProgram/Translate'/file);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def word(s):return list(map(int,s.split(',')))
def coeff(xs):return tuple(zip(xs[::2],xs[1::2]))
def module_poly(s):
 require(type(s)is str,'native module code must be a known string, including explicit empty zero')
 return [(coeff((xs:=word(w))[:-1]),xs[-1]) for w in s.split(';')] if s else []
def ring_poly(s):
 require(type(s)is str,'native scalar code must be a known string')
 return [coeff(word(w)) for w in s.split(';')] if s else []
def expanded(mon):return [i for i,a in mon for _ in range(a)]
def ring_literal(s):return [expanded(m)for m in ring_poly(s)]
def term_literal(ts):return '['+', '.join(f'({j}, {lit([expanded(c)])})' for c,j in ts)+']'
def chars(s):return '['+', '.join("'\\n'"if c=='\n'else repr(c)for c in s)+']'
def word_expression(xs):
 if len(xs)==1:return f'(imageTerms ⟨{xs[0]}, by decide⟩)'
 return f'(scaleTerms [{lit([xs[0]]*xs[1])}] {word_expression(xs[2:])})'

def read_inputs(root,witness):
 mp=load(root,'module_presentations','generate-module-presentations.py');mg=load(root,'module_maps','generate-module-maps.py');native=load(root,'native_contract','native-contract.py');low=native.load_lowstem()
 archive=root/'Source/LWXMachine/kervaire_database.rar'
 modules=mp.read_inputs(root,archive);mp.check_outputs(root/'KIP126/LinProgram/Generated/Modules',mp.build_outputs(modules))
 graphs=mg.read_inputs(root,archive);go=mg.build_outputs(graphs);mg.check_outputs(root/'KIP126/LinProgram/Generated/ModuleMaps',go);mg.check_registered_outputs(root,go)
 source=next(m for m in modules if m['object']=='CW_nu_eta');target=next(m for m in modules if m['object']=='Ceta');graph=next(g for g in graphs if g['native_name']=='CW_nu_eta__Ceta')
 require((source['generator_count'],source['relation_count'],target['generator_count'],target['relation_count'])==(844,69263,887,76569),'complete native module contract changed')
 require([r['id'] for r in graph['rows']]==list(range(844)),'graph must retain every ordered original image')
 spath,sraw,ssha=low.pinned('S0_AdamsSS_t261.db');db=native.connect(spath);sphere=[dict(r)for r in db.execute('SELECT rowid AS sqlite_rowid,* FROM S0_AdamsE2_relations ORDER BY rowid')];db.close()
 require(len(sphere)==231848,'full original scalar relation count changed')
 byid,details,stats=check_witnesses(source,target,graph,sphere,[json.loads(line)for line in witness.read_text().splitlines()],low)
 provenance={'source_module':source['provenance'],'target_module':target['provenance'],'native_graph':graph['provenance'],'sphere_database':{'sha256':ssha,'size':len(sraw)},'generator_count':844,'target_generator_count':887,'all_relation_count':69263,'target_relation_count':76569,**stats}
 return source,target,graph,sphere,byid,details,provenance

def check_witnesses(source,target,graph,sphere,rows,low):
 ring={r['sqlite_rowid']:ring_poly(r['rel'])for r in sphere};mod={r['sqlite_rowid']:module_poly(r['rel'])for r in target['relations']};images={r['id']:module_poly(r['map'])for r in graph['rows']}
 byid={};ids={r['sqlite_rowid'] for r in source['relations']}
 for w in rows:
  require(set(w)=={'source_relation_rowid','source_degree','terms'},'unknown witness fields')
  require(isinstance(w['source_degree'],list)and len(w['source_degree'])==2 and all(type(a)is int for a in w['source_degree']),'invalid source degree')
  rid=w['source_relation_rowid'];require(type(rid)is int and rid in ids and rid not in byid,'unknown or duplicate witness source ID');byid[rid]=w
  require(isinstance(w['terms'],list)and w['terms'],'nonzero image needs a nonempty combination')
  for t in w['terms']:
   require(set(t)=={'kind','rowid','multiplier','module_generator'},'unknown witness term fields')
   require(t['kind']in ('ring','module'),'unknown witness kind')
   require(type(t['rowid'])is int and t['rowid']in (ring if t['kind']=='ring'else mod),'unknown original target relation ID')
   j=t['module_generator'];require(type(j)is int and 0<=j<887 if t['kind']=='ring'else j is None,'wrong module generator / relation kind')
   fac=t['multiplier'];require(isinstance(fac,list)and all(isinstance(a,list)and len(a)==2 and type(a[0])is int and 0<=a[0]<2914 and type(a[1])is int and 0<a[1]<=200 for a in fac),'invalid multiplier')
   require([a[0]for a in fac]==sorted({a[0]for a in fac}),'multiplier IDs must be strictly ordered')
 details={};nonzero=set();steps=0;max_support=0
 for r in source['relations']:
  rid=r['sqlite_rowid'];inp=[(low.mul(c,d),j)for c,i in module_poly(r['rel'])for d,j in images[i]];parity=set()
  for t in inp:parity.symmetric_difference_update({t})
  require((rid in byid)==bool(parity),'witness coverage must exactly match formal nonzero images: '+str(rid))
  w=byid.get(rid,{'terms':[]});support={j for _,j in inp}
  if rid in byid:
   nonzero.add(rid);require(w['source_degree']==[r['s'],r['t']],'source witness degree changed')
  for t in w['terms']:
   fac=tuple(map(tuple,t['multiplier']));terms=mod[t['rowid']]if t['kind']=='module'else [(m,t['module_generator'])for m in ring[t['rowid']]]
   support.update(j for _,j in terms)
   for c,j in terms:parity.symmetric_difference_update({(low.mul(fac,c),j)})
  require(not parity,'auxiliary combination fails original full target coordinates: '+str(rid))
  steps+=len(w['terms']);max_support=max(max_support,len(support));details[rid]=(inp,sorted(support))
 require(set(byid)==nonzero,'extra witness IDs')
 return byid,details,{'nonzero_image_relations':len(nonzero),'formal_zero_relations':len(source['relations'])-len(nonzero),'witness_steps':steps,'maximum_support_envelope':max_support}

def build(root,out,witness,shared):
 source,target,graph,sphere,byid,details,provenance=read_inputs(root,witness)
 ring={r['sqlite_rowid']:r for r in sphere};mods={r['sqlite_rowid']:r for r in target['relations']}
 used_ring={t['rowid']for w in byid.values()for t in w['terms']if t['kind']=='ring'};used_mod={t['rowid']for w in byid.values()for t in w['terms']if t['kind']=='module'}
 outputs={};jobs=[]
 def emit(module,text,kind):
  text=lean_module(text);b=text.encode();path='src/'+module.replace('.','/')+'.lean';require(path not in outputs,'duplicate generated module');outputs[path]=b;jobs.append({'module':module,'source':path,'sha256':sha(b),'kind':kind,'imports':re.findall(r'^(?:public )?import ([\w.]+)$',text,re.M)})
 # Mathematical support is imported from the repository, never reimplemented.
 support_paths=[root/'KIP126/LinProgram/Certificates/ModuleMaps'/f'{name}.lean' for name in ('Support','ModuleSupport','ModuleTerms')]
 for p in support_paths:require(p.is_file(),'missing repository mathematical support: '+str(p))
 shared_manifest=json.loads((shared/'manifest.json').read_text());shared_jobs={j['module']:j for j in shared_manifest['jobs']};shared_ids={};shared_hashes={}
 for name,j in shared_jobs.items():
  if '.Shared.SphereRelations'not in name:continue
  text=(shared/j['source']).read_text();require(sha(text.encode())==j['sha256'],'shared sphere proof source changed')
  for rid in re.findall(r'^def ring(\d+) :',text,re.M):require(int(rid)not in shared_ids,'duplicate shared ring ID');shared_ids[int(rid)]=name
 needed_shared=sorted({shared_ids[i]for i in used_ring if i in shared_ids})
 copied=set()
 def copy_shared(name):
  if name in copied:return
  j=shared_jobs[name];text=(shared/j['source']).read_text();require(sha(text.encode())==j['sha256'],'shared source hash changed')
  for imp in j['imports']:
   if '.Shared.'in imp:copy_shared(imp)
  emit(name,text,j['kind']);copied.add(name);shared_hashes[name]=j['sha256']
 for name in needed_shared:copy_shared(name)
 extras=sorted(used_ring-set(shared_ids));extra_groups={}
 for rid in extras:extra_groups.setdefault(max(0,(rid-4)//1024),[]).append(rid)
 for ci,rids in sorted(extra_groups.items()):
  chunk_name=BASE+f'.Shared.SphereChunk{ci:03d}'
  if chunk_name not in copied:
   if chunk_name in shared_jobs:copy_shared(chunk_name)
   else:
    codes=[r['rel']for r in sphere[3+ci*1024:3+(ci+1)*1024]];space=NS+f'.SphereChunk{ci:03d}'
    emit(chunk_name,f'import {BASE}.Support\nimport {BASE}.ModuleSupport\n'+HEADER+f'''namespace {space}
def rows : List (List Char) := ['''+',\n'.join(map(chars,codes))+f''']
theorem transcription : RawData.relationChunks[{ci}] = String.ofList (joinRows rows) := by rfl
theorem no_newline : ∀ row ∈ rows, '\\n' ∉ row := by decide
theorem member (j : Fin {len(codes)}) :
    String.ofList (rows[j.val]'(by change j.val < {len(codes)}; exact j.isLt)) ∈ RawData.relations :=
  rawChunk_mem {ci} (by decide) rows transcription no_newline _ (List.getElem_mem _)
end {space}
''','sphere_chunk');copied.add(chunk_name)
  parts=[f'import {chunk_name}\nimport {BASE}.ModuleSupport\n'+HEADER+f'namespace {NS}\n']
  for rid in rids:
   raw=ring[rid]['rel'];words=[word(t)for t in raw.split(';')];mem='exact List.mem_append_left _ (by simp [RawData.firstRelations])'if rid<=3 else f'exact SphereChunk{ci:03d}.member ⟨{(rid-4)%1024}, by decide⟩'
   parts.append(f'''def ring{rid} : Polynomial := {lit(ring_literal(raw))}
theorem ring{rid}_zero : evaluate nativeScalar ring{rid} = 0 := by
  have hp : (({lit(raw)}.splitOn ";").map fun w => if w = "" then [] else
      (w.splitOn ",").map (fun a => a.toNat?.getD 0)) = {lit(words)} := by cbv
  have he : evaluate nativeVariable ring{rid} = relationPolynomial {lit(raw)} := by
    rw [relationPolynomial_words, hp]
    simp [ring{rid}, evaluate, evaluateMonomial, nativeVariable,
      polynomialOfPowers, RawData.generatorCount, pow_succ, mul_assoc]
  rw [← projection_evaluate, he]
  apply csv_relation_zero
  {mem}
''')
  parts.append(f'end {NS}\n');emit(BASE+f'.CWShared.SphereRelations{ci:03d}','\n'.join(parts),'sphere_relations')
 emit(BASE+'.CWToCeta.Data',f'''import {BASE}.Support
import {BASE}.ModuleTerms
import KIP126.LinProgram.Generated.ModuleMaps.CWToCeta
import KIP126.LinProgram.Model.Modules
{HEADER}
namespace {CW}
noncomputable def generatorImage (i : KIP126.LinModule.CWNuEta.Generator) : KIP126.LinModule.Ceta.Model :=
  nativeModuleImage 887 KIP126.LinModule.RawData.Ceta.relations
    (KIP126.LinModule.RawData.Maps.CWToCeta.imageCode i)
def imageTerms (i : KIP126.LinModule.CWNuEta.Generator) : ModuleTerms 887 :=
  nativeModuleTerms 887 (KIP126.LinModule.RawData.Maps.CWToCeta.imageCode i)
theorem imageTerms_evaluate (i : KIP126.LinModule.CWNuEta.Generator) :
    ModuleExpressions.evaluate nativeScalar KIP126.LinModule.Ceta.generator
      (termsExpression (imageTerms i)) = generatorImage i :=
  evaluate_nativeModuleTerms 887 KIP126.LinModule.RawData.Ceta.relations _
end {CW}
''','data')
 parts=[f'import {BASE}.CWToCeta.Data\n'+HEADER+f'namespace {CW}\n']
 for r in graph['rows']:
  i=r['id'];parts.append(f'''theorem image{i}_terms : imageTerms ⟨{i}, by decide⟩ = {term_literal(module_poly(r['map']))} := by
  have hi : KIP126.LinModule.RawData.Maps.CWToCeta.imageCode ⟨{i}, by decide⟩ = {lit(r['map'])} := by
    simp only [KIP126.LinModule.RawData.Maps.CWToCeta.imageCode, KIP126.LinModule.RawData.Maps.CWToCeta.imageCodes, Array.getElem_map]
    rfl
  unfold imageTerms
  erw [hi]
  cbv
''')
 parts.append(f'end {CW}\n');emit(BASE+'.CWToCeta.Images','\n'.join(parts),'images')
 mod_groups={}
 for rid in sorted(used_mod):mod_groups.setdefault((rid-1)//512,[]).append(rid)
 for ci,rids in sorted(mod_groups.items()):
  parts=[f'import {BASE}.CWToCeta.Data\n'+HEADER+f'namespace {CW}\n']
  for rid in rids:
   raw=mods[rid]['rel'];parts.append(f'''def module{rid} : ModuleTerms 887 := {term_literal(module_poly(raw))}
theorem module{rid}_zero : ModuleExpressions.evaluate nativeScalar KIP126.LinModule.Ceta.generator
    (termsExpression module{rid}) = 0 := by
  change ModuleExpressions.evaluate nativeScalar
    (KIP126.LinModule.Presentation.generator 887 KIP126.LinModule.RawData.Ceta.relations)
    (termsExpression module{rid}) = 0
  have hp : moduleRelationTerms 887 {lit(raw)} = module{rid} := by cbv
  rw [← hp, evaluate_moduleRelationTerms]
  apply KIP126.LinModule.Presentation.native_relation_zero
  exact KIP126.LinModule.Presentation.relation_mem_of_chunk
    KIP126.LinModule.RawData.Ceta.relationChunks {ci} (by decide) _
    (List.mem_of_getElem? (i := {(rid-1)%512}) (by rfl))
''')
  parts.append(f'end {CW}\n');emit(BASE+f'.CWShared.ModuleRelations{ci:03d}','\n'.join(parts),'module_relations')
 block_count=(len(source['relations'])+511)//512
 for bi in range(block_count):
  rows=source['relations'][bi*512:(bi+1)*512];needed=set()
  for r in rows:
   for t in byid.get(r['sqlite_rowid'],{'terms':[]})['terms']:
    rid=t['rowid'];needed.add(BASE+f'.CWShared.ModuleRelations{(rid-1)//512:03d}'if t['kind']=='module'else shared_ids.get(rid,BASE+f'.CWShared.SphereRelations{max(0,(rid-4)//1024):03d}'))
  space=CW+f'.Relations{bi:03d}';parts=[f'import {BASE}.CWToCeta.Images\n'+''.join(f'import {n}\n'for n in sorted(needed))+HEADER+f'namespace {space}\n']
  for r in rows:
   rid=r['sqlite_rowid'];code=r['rel'];inp,support=details[rid];w=byid.get(rid,{'terms':[]});keys=sorted({(t['kind'],t['rowid'],t['module_generator'])for t in w['terms']});rex=[f'module{i}'if k=='module'else f'[({j}, ring{i})]' for k,i,j in keys];rels='['+', '.join(rex)+']';terms='['+', '.join(f'⟨{keys.index((t["kind"],t["rowid"],t["module_generator"]))}, {lit([expanded(t["multiplier"])])}⟩'for t in w['terms'])+']';words=[word(w)for w in code.split(';')];gids=sorted({w[-1]for w in words})
   ie='[]'
   for ws in reversed(words):ie=word_expression(ws)+' ++ ('+ie+')'
   parts.append(f'''def support{rid} : Fin {len(support)} ↪ Fin 887 :=
  ⟨(![{', '.join(map(str,support))}] : Fin {len(support)} → Fin 887), by decide⟩
def input{rid} : ModuleTerms 887 := {term_literal(inp)}
def rels{rid} : List (ModuleTerms 887) := {rels}
def witness{rid} : List Term := {terms}
theorem supported{rid} : (input{rid} :: rels{rid}).all (termsSupported support{rid}) = true := by decide
theorem check{rid} : ModuleExpressions.check
    (rels{rid}.map fun ts => restrict support{rid} (termsExpression ts))
    (restrict support{rid} (termsExpression input{rid})) ModuleExpressions.zero witness{rid} = true := by decide
/-- Original source row {rid}, degree ({r['s']},{r['t']}), in the entire original target quotient. -/
theorem row{rid}_zero :
    KIP126.LinModule.Presentation.evaluateRelation generatorImage {lit(code)} = 0 := by
  have hp : (({lit(code)}.splitOn ";").map fun w =>
      (w.splitOn ",").map (fun a => a.toNat?.getD 0)) = {lit(words)} := by cbv
  have hs : substituteModuleRelation imageTerms {lit(code)} = input{rid} := by
    rw [substituteModuleRelation_words, hp]
    simp only [List.flatMap_cons, List.flatMap_nil]
    change {ie} = _
    rw [{', '.join(f'image{i}_terms'for i in gids)}]
    decide
  have hz : ModuleExpressions.evaluate nativeScalar KIP126.LinModule.Ceta.generator
      (termsExpression input{rid}) = 0 := by
    apply check_terms_projection_zero _ support{rid} rels{rid} input{rid} witness{rid} supported{rid} check{rid}
''')
   if not keys:parts.append('    simp [rels'+str(rid)+']\n')
   else:
    parts.append(f'    intro ts hts\n    simp only [rels{rid}, List.mem_cons, List.not_mem_nil, or_false] at hts\n')
    if len(keys)==1:parts.append('    subst ts\n')
    else:parts.append('    rcases hts with '+' | '.join(['rfl']*len(keys))+'\n')
    for k,i,j in keys:parts.append(('    'if len(keys)==1 else '    · ')+(f'exact module{i}_zero'if k=='module'else f'exact evaluate_single_terms_zero _ {j} ring{i} ring{i}_zero')+'\n')
   parts.append(f'''  rw [← hs, evaluate_substituteModuleRelation] at hz
  have himage : (fun j => ModuleExpressions.evaluate nativeScalar KIP126.LinModule.Ceta.generator
      (termsExpression (imageTerms j))) = generatorImage := funext imageTerms_evaluate
  simpa only [himage] using hz
''')
  parts.append(f'''theorem all_relations_zero :
    ∀ code ∈ KIP126.LinModule.RawData.CWNuEta.relationChunk{bi},
      KIP126.LinModule.Presentation.evaluateRelation generatorImage code = 0 := by
  simp only [KIP126.LinModule.RawData.CWNuEta.relationChunk{bi}, List.forall_mem_cons, List.forall_mem_nil]
  exact ⟨'''+', '.join(f'row{r["sqlite_rowid"]}_zero'for r in rows)+''', (by simp)⟩
''')
  parts.append(f'end {space}\n');emit(BASE+f'.CWToCeta.Relations{bi:03d}','\n'.join(parts),'relations')
 text=''.join(f'import {BASE}.CWToCeta.Relations{bi:03d}\n'for bi in range(block_count))+HEADER+f'''namespace {CW}
theorem all_relations_zero :
    ∀ code ∈ KIP126.LinModule.RawData.CWNuEta.relations,
      KIP126.LinModule.Presentation.evaluateRelation generatorImage code = 0 := by
  have hblocks : ∀ block ∈ KIP126.LinModule.RawData.CWNuEta.relationChunks.toList,
      ∀ code ∈ block, KIP126.LinModule.Presentation.evaluateRelation generatorImage code = 0 := by
    change ∀ block ∈ ['''+', '.join(f'KIP126.LinModule.RawData.CWNuEta.relationChunk{bi}'for bi in range(block_count))+f'''],
      ∀ code ∈ block, KIP126.LinModule.Presentation.evaluateRelation generatorImage code = 0
    simp only [List.forall_mem_cons, List.forall_mem_nil]
    exact ⟨'''+', '.join(f'Relations{bi:03d}.all_relations_zero'for bi in range(block_count))+f''', (by simp)⟩
  intro code hcode
  obtain ⟨block, hblock, hcode⟩ := List.mem_flatten.mp hcode
  exact hblocks block hblock code hcode
noncomputable def nativeMap : KIP126.LinModule.CWNuEta.Model →ₗ[E2] KIP126.LinModule.Ceta.Model :=
  KIP126.LinModule.Presentation.desc generatorImage _ all_relations_zero
theorem nativeMap_generator (i : KIP126.LinModule.CWNuEta.Generator) :
    nativeMap (KIP126.LinModule.CWNuEta.generator i) = generatorImage i :=
  KIP126.LinModule.Presentation.desc_generator generatorImage _ all_relations_zero i
theorem nativeMap_monomial (code : String) :
    nativeMap (KIP126.LinModule.CWNuEta.monomial code) =
      KIP126.LinModule.Presentation.evaluatePowers generatorImage
        ((code.splitOn ",").map (fun a => a.toNat?.getD 0)) :=
  KIP126.LinModule.Presentation.desc_monomialVector generatorImage _ all_relations_zero code
theorem nativeMap_unique (f : KIP126.LinModule.CWNuEta.Model →ₗ[E2] KIP126.LinModule.Ceta.Model)
    (h : ∀ i, f (KIP126.LinModule.CWNuEta.generator i) = generatorImage i) : f = nativeMap :=
  KIP126.LinModule.Presentation.desc_unique generatorImage _ all_relations_zero f h
end {CW}
''';emit(BASE+'.CWToCeta.Proofs',text,'final')
 checks=f'''import {BASE}.CWToCeta.Proofs
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def.StageInput).isPrefixOf mod || mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "native full module map imports a model/delivery or basis premise: {{mod}}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``{CW}.imageTerms_evaluate, ``{CW}.all_relations_zero,
      ``{CW}.nativeMap, ``{CW}.nativeMap_generator,
      ``{CW}.nativeMap_monomial, ``{CW}.nativeMap_unique] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected full module map axiom: {{decl}}: {{ax}}"
#print axioms {CW}.all_relations_zero
#print axioms {CW}.nativeMap
''';emit(BASE+'.CWToCeta.Checks',checks,'audit')
 names={j['module']for j in jobs}
 for j in jobs:j['dependencies']=[i for i in j['imports']if i in names]
 inputs={str(p.relative_to(root)):sha(p.read_bytes())for p in [root/'lean-toolchain',root/'lake-manifest.json',root/'KIP126/LinProgram/Generated/ModuleMaps/CWToCeta.lean',root/'KIP126/LinProgram/Generated/Modules/CWNuEta.lean',root/'KIP126/LinProgram/Generated/Modules/Ceta.lean',root/'KIP126/LinProgram/Generated/E2.lean']}
 manifest={'schema':'lin-native-complete-cw-certificate-build/v2-repository-support','source_root':str(root),'provenance':provenance,'pinned_source_hashes':inputs,'auxiliary_witness':{'path':'witness/CWToCeta.jsonl','sha256':sha(witness.read_bytes()),'size':witness.stat().st_size},'generation_inputs':{str(p.resolve()):sha(p.read_bytes())for p in [pathlib.Path(__file__),pathlib.Path(__file__).with_name('rebuild-cw-witness.py'),pathlib.Path(__file__).with_name('replay-cw.py'),*support_paths,root/'KIP126/LinProgram/Translate/lean_module.py',root/'KIP126/LinProgram/Translate/generate-module-presentations.py',root/'KIP126/LinProgram/Translate/generate-module-maps.py',root/'KIP126/LinProgram/Translate/native-contract.py',root/'KIP126/LinProgram/Translate/replay-lowstem.py',root/'KIP126/LinProgram/Translate/check-branch-d2-coordinates.py']},'shared_source_root':str(shared.resolve()),'shared_source_hashes':shared_hashes,'shared_source_manifest_sha256':sha((shared/'manifest.json').read_bytes()),'all_relation_count':69263,'source_blocks':block_count,'ring_relation_count':len(used_ring),'reused_ring_relation_count':len(used_ring&set(shared_ids)),'new_ring_relation_count':len(extras),'module_relation_count':len(used_mod),'generator_count':844,'target_generator_count':887,'native_graph_bound_in_definition':True,'empty_native_image_semantics':'zero','quotient_map_certified':False,'actual_model_comparison_certified':False,'jobs':jobs}
 outputs['manifest.json']=canonical(manifest);outputs['witness/CWToCeta.jsonl']=witness.read_bytes();return outputs

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=pathlib.Path,required=True);ap.add_argument('--output-dir',type=pathlib.Path,required=True);ap.add_argument('--witness',type=pathlib.Path,required=True);ap.add_argument('--shared-ceta',type=pathlib.Path,required=True);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 outputs=build(args.root.resolve(),args.output_dir.resolve(),args.witness.resolve(),args.shared_ceta.resolve())
 for rel,data in outputs.items():
  dest=args.output_dir/rel
  if args.check:require(dest.is_file()and dest.read_bytes()==data,'generated output mismatch: '+rel)
  else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 expected={rel for rel in outputs if rel.endswith('.lean')};actual={str(p.relative_to(args.output_dir))for p in (args.output_dir/'src').rglob('*.lean')};require(actual==expected,'stale or missing generated Lean modules')
 print(('Checked'if args.check else 'Generated')+f' complete CW plan: {len(expected)} Lean modules, 844 official images, all 69263 original relations.',flush=True)
if __name__=='__main__':main()
