#!/usr/bin/env python3
"""Generate complete native Ceta-to-S0 quotient certificates from pinned inputs.
The witness is auxiliary, untrusted F2 ideal-combination data. Every source
relation is replayed against fresh authenticated native entities before Lean
sources are emitted. The existing NamedElement checker remains the proof kernel.
"""
import argparse, hashlib, importlib.util, json, pathlib, re, shutil

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent.parent))
from lean_module import lean_module, module_output
BASE='KIP126.LinProgram.Certificates.ModuleMaps'
NS='KIP126.LinModule.NativeMapCertificates'
CETA='KIP126.LinModule.CetaToSphere'
HEADER=f'''open NamedElementCertificates
open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open {NS}
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

def read_inputs(root,witness):
 mp=load(root,'module_presentations','generate-module-presentations.py');mg=load(root,'module_maps','generate-module-maps.py');native=load(root,'native_contract','native-contract.py');low=native.load_lowstem()
 archive=root/'Source/LWXMachine/kervaire_database.rar'
 modules=mp.read_inputs(root,archive);mp.check_outputs(root/'KIP126/LinProgram/Generated/Modules',mp.build_outputs(modules))
 graphs=mg.read_inputs(root,archive);graph_outputs=mg.build_outputs(graphs);mg.check_outputs(root/'KIP126/LinProgram/Generated/ModuleMaps',graph_outputs);mg.check_registered_outputs(root,graph_outputs)
 ceta=next(m for m in modules if m['object']=='Ceta');graph=next(g for g in graphs if g['native_name']=='Ceta__S0')
 require(ceta['generator_count']==887 and ceta['relation_count']==76569,'complete Ceta contract changed')
 images=graph['rows'];require([r['id']for r in images]==list(range(887)),'native graph is not complete ordered IDs')
 spath,sraw,ssha=low.pinned('S0_AdamsSS_t261.db');db=native.connect(spath);sphere=[dict(r)for r in db.execute('SELECT rowid AS sqlite_rowid,* FROM S0_AdamsE2_relations ORDER BY rowid')];db.close()
 require(len(sphere)==231848,'complete sphere relation count changed')
 def poly(code):
  ans=set()
  for term in code.split(';') if code else []:ans.symmetric_difference_update({low.mon(term)})
  return ans
 ring={r['sqlite_rowid']:poly(r['rel'])for r in sphere};ivals={r['id']:poly(r['map'])for r in images}
 rows=[json.loads(line)for line in witness.read_text().splitlines()];byid={r['source_relation_rowid']:r for r in rows}
 require(len(byid)==len(rows),'duplicate witness source IDs')
 nonzero=set();steps=0
 for source in ceta['relations']:
  original=set()
  for term in source['rel'].split(';'):
   xs=list(map(int,term.split(',')));require(len(xs)%2==1,'bad source term');factor=tuple(zip(xs[:-1:2],xs[1:-1:2]))
   for mon in ivals[xs[-1]]:original.symmetric_difference_update({low.mul(factor,mon)})
  rid=source['sqlite_rowid']
  if not original:
   require(rid not in byid,'unexpected witness for formal-zero source row');continue
  nonzero.add(rid);require(rid in byid,'missing source relation witness')
  w=byid[rid];require(set(w)=={'source_relation_rowid','source_degree','terms'},'unknown witness fields')
  require(w['source_degree']==[source['s'],source['t']],'source witness degree changed')
  require(isinstance(w['terms'],list)and w['terms'],'missing nonzero witness combination')
  for t in w['terms']:
   require(set(t)=={'kind','rowid','multiplier','module_generator'},'unknown witness term fields')
   require(t['kind']=='ring'and t['module_generator']is None,'non-ring term in sphere target')
   require(type(t['rowid'])is int and t['rowid']in ring,'unknown native sphere relation row')
   fac=t['multiplier'];require(isinstance(fac,list)and all(isinstance(a,list)and len(a)==2 and type(a[0])is int and 0<=a[0]<2914 and type(a[1])is int and a[1]>0 for a in fac),'invalid multiplier')
   require([a[0]for a in fac]==sorted({a[0]for a in fac}),'multiplier IDs must be strictly ordered')
   for mon in ring[t['rowid']]:original.symmetric_difference_update({low.mul(tuple(map(tuple,fac)),mon)})
  require(not original,'untrusted combination does not prove source relation '+str(rid));steps+=len(w['terms'])
 require(set(byid)==nonzero,'witness coverage is not exactly every nonzero source image')
 return ceta,graph,sphere,byid,{'source_module':ceta['provenance'],'native_graph':graph['provenance'],'sphere_database':{'sha256':ssha,'size':len(sraw)},'generator_count':887,'all_relation_count':76569,'nonzero_image_relations':len(nonzero),'formal_zero_relations':76569-len(nonzero),'witness_steps':steps}

def powers(s):return list(map(int,s.split(','))) if s else []
def expanded(s):
 xs=powers(s);return [i for i,a in zip(xs[::2],xs[1::2])for _ in range(a)]
def poly(s):return [expanded(m)for m in s.split(';')]if s else []
def chars(s):return '['+', '.join("'\\n'"if c=='\n'else repr(c)for c in s)+']'
def word_expression(xs):
 if len(xs)==1:return f'(imagePolynomial ⟨{xs[0]}, by decide⟩)'
 return f'(NamedElementCertificates.multiply [{lit([xs[0]]*xs[1])}] {word_expression(xs[2:])})'

def build(root,out,witness):
 ceta,graph,sphere,byid,provenance=read_inputs(root,witness);ring={r['sqlite_rowid']:r for r in sphere};images=graph['rows'];used=sorted({t['rowid']for w in byid.values()for t in w['terms']});chunks=sorted({(rid-4)//1024 for rid in used if rid>=4});outputs={};jobs=[]
 def emit(module,text,kind):
  text=lean_module(text);b=text.encode();path='src/'+module.replace('.','/')+'.lean';outputs[path]=b
  jobs.append({'module':module,'source':path,'sha256':sha(b),'kind':kind,'imports':re.findall(r'^(?:public )?import ([\w.]+)$',text,re.M)})
 support=root/'KIP126/LinProgram/Certificates/ModuleMaps/Support.lean'
 require(support.is_file(), 'repository native map support is required')
 emit(BASE+'.CetaToSphere.Data',f'''import {BASE}.Support
import KIP126.LinProgram.Generated.ModuleMaps.CetaToSphere
import KIP126.LinProgram.Model.Modules
import KIP126.LinProgram.Model.ModulePresentation.Maps
{HEADER}
namespace {CETA}
/-- The entire official native graph determines the proposed image family.
The graph's empty string is the recorded zero, never a missing default. -/
noncomputable def generatorImage (i : KIP126.LinModule.Ceta.Generator) : E2 :=
  nativeImage (KIP126.LinModule.RawData.Maps.CetaToSphere.imageCode i)

def imagePolynomial (i : KIP126.LinModule.Ceta.Generator) : Polynomial :=
  parseNativeCode (KIP126.LinModule.RawData.Maps.CetaToSphere.imageCode i)

theorem imagePolynomial_evaluate (i : KIP126.LinModule.Ceta.Generator) :
    evaluate nativeScalar (imagePolynomial i) = generatorImage i :=
  evaluate_parseNativeCode _

theorem image_zero : generatorImage ⟨0, by decide⟩ = 0 := by
  have hz : KIP126.LinModule.RawData.Maps.CetaToSphere.imageCode ⟨0, by decide⟩ = "" := by
    simp only [KIP126.LinModule.RawData.Maps.CetaToSphere.imageCode, KIP126.LinModule.RawData.Maps.CetaToSphere.imageCodes, Array.getElem_map]
    rfl
  unfold generatorImage
  erw [hz]
  simp [nativeImage]
end {CETA}
''','data')
 images_parts=[f'import {BASE}.CetaToSphere.Data\n'+HEADER+f'namespace {CETA}\n']
 for r in images:
  i=r['id'];images_parts.append(f'''theorem image{i}_polynomial : imagePolynomial ⟨{i}, by decide⟩ = {lit(poly(r['map']))} := by
  have hi : KIP126.LinModule.RawData.Maps.CetaToSphere.imageCode ⟨{i}, by decide⟩ = {lit(r['map'])} := by
    simp only [KIP126.LinModule.RawData.Maps.CetaToSphere.imageCode, KIP126.LinModule.RawData.Maps.CetaToSphere.imageCodes, Array.getElem_map]
    rfl
  unfold imagePolynomial
  erw [hi]
  cbv
''')
 images_parts.append(f'end {CETA}\n');emit(BASE+'.CetaToSphere.Images','\n'.join(images_parts),'images')
 for ci in chunks:
  codes=[r['rel']for r in sphere[3+ci*1024:3+(ci+1)*1024]];space=NS+f'.SphereChunk{ci:03d}'
  text=f'import {BASE}.Support\n'+HEADER+f'''namespace {space}
def rows : List (List Char) := ['''+',\n'.join(map(chars,codes))+f''']
theorem transcription : RawData.relationChunks[{ci}] = String.ofList (joinRows rows) := by rfl
theorem no_newline : ∀ row ∈ rows, '\\n' ∉ row := by decide
theorem member (j : Fin {len(codes)}) :
    String.ofList (rows[j.val]'(by change j.val < {len(codes)}; exact j.isLt)) ∈ RawData.relations :=
  rawChunk_mem {ci} (by decide) rows transcription no_newline _ (List.getElem_mem _)
end {space}
''';emit(BASE+f'.Shared.SphereChunk{ci:03d}',text,'sphere_chunk')
 groups={ci:[rid for rid in used if max(0,(rid-4)//1024)==ci]for ci in chunks}
 for ci,ids in groups.items():
  parts=[f'import {BASE}.Shared.SphereChunk{ci:03d}\n'+HEADER+f'namespace {NS}\n']
  for rid in ids:
   raw=ring[rid]['rel'];words=[powers(t)for t in raw.split(';')]
   mem='exact List.mem_append_left _ (by simp [RawData.firstRelations])'if rid<=3 else f'exact SphereChunk{ci:03d}.member ⟨{(rid-4)%1024}, by decide⟩'
   parts.append(f'''def ring{rid} : Polynomial := {lit(poly(raw))}
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
  parts.append(f'end {NS}\n');emit(BASE+f'.Shared.SphereRelations{ci:03d}','\n'.join(parts),'sphere_relations')
 block_count=(len(ceta['relations'])+511)//512
 for bi in range(block_count):
  source=ceta['relations'][bi*512:(bi+1)*512];needed=sorted({max(0,(t['rowid']-4)//1024)for r in source for t in byid.get(r['sqlite_rowid'],{'terms':[]})['terms']});space=CETA+f'.Relations{bi:03d}'
  parts=[f'import {BASE}.CetaToSphere.Images\n'+''.join(f'import {BASE}.Shared.SphereRelations{ci:03d}\n'for ci in needed)+HEADER+f'namespace {space}\n']
  for r in source:
   rid=r['sqlite_rowid'];code=r['rel'];words=[powers(t)for t in code.split(';')];w=byid.get(rid,{'terms':[]});rids=sorted({t['rowid']for t in w['terms']});rels='['+', '.join('ring'+str(i)for i in rids)+']';terms='['+', '.join(f'⟨{rids.index(t["rowid"])}, {lit([[i for i,a in t["multiplier"]for _ in range(a)]])}⟩'for t in w['terms'])+']';inp=[]
   for word in words:
    coeff=expanded(','.join(map(str,word[:-1])));inp.extend(sorted(coeff+m)for m in poly(images[word[-1]]['map']))
   expr='[]'
   for word in reversed(words):expr=word_expression(word)+' ++ ('+expr+')'
   gids=sorted({word[-1]for word in words})
   parts.append(f'''def input{rid} : Polynomial := {lit(inp)}
theorem check{rid} : check {rels} input{rid} [] {terms} = true := by decide
/-- Exact native source row {rid}, degree ({r['s']},{r['t']}); image in the original E2. -/
theorem row{rid}_zero :
    KIP126.LinModule.Presentation.evaluateRelation generatorImage {lit(code)} = 0 := by
  have hp : (({lit(code)}.splitOn ";").map fun w =>
      (w.splitOn ",").map (fun a => a.toNat?.getD 0)) = {lit(words)} := by cbv
  have hs : {lit(words)}.flatMap (substituteWord imagePolynomial) = input{rid} := by
    simp only [List.flatMap_cons, List.flatMap_nil]
    change {expr} = _
    rw ['''+', '.join(f'image{i}_polynomial'for i in gids)+f''']
    decide
  have hz : evaluate nativeScalar input{rid} = 0 := by
    apply check_projection_zero {rels} _ {terms} check{rid}
''')
   if not rids:parts.append('    simp\n')
   else:
    parts.append('    intro r hr\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr\n')
    if len(rids)==1:parts.append(f'    subst r\n    exact ring{rids[0]}_zero\n')
    else:
     parts.append('    rcases hr with '+' | '.join(['rfl']*len(rids))+'\n');parts.extend(f'    · exact ring{i}_zero\n'for i in rids)
   parts.append(f'''  rw [evaluateRelation_words, hp]
  rw [← hs] at hz
  have hzero : evaluate nativeScalar ([] : Polynomial) = 0 := rfl
  have himage : (fun j => evaluate nativeScalar (imagePolynomial j)) = generatorImage :=
    funext imagePolynomial_evaluate
  simpa only [List.flatMap_cons, List.flatMap_nil, evaluate_append, evaluate_substituteWord,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hzero, himage] using hz
''')
  parts.append(f'''theorem all_relations_zero :
    ∀ code ∈ KIP126.LinModule.RawData.Ceta.relationChunk{bi},
      KIP126.LinModule.Presentation.evaluateRelation generatorImage code = 0 := by
  simp only [KIP126.LinModule.RawData.Ceta.relationChunk{bi}, List.forall_mem_cons, List.forall_mem_nil]
  exact ⟨'''+', '.join(f'row{r["sqlite_rowid"]}_zero'for r in source)+''', (by simp)⟩
''')
  parts.append(f'end {space}\n');emit(BASE+f'.CetaToSphere.Relations{bi:03d}','\n'.join(parts),'relations')
 # All original source blocks, with no subset or degree qualifier.
 text=''.join(f'import {BASE}.CetaToSphere.Relations{bi:03d}\n'for bi in range(block_count))+HEADER+f'''namespace {CETA}
theorem all_relations_zero :
    ∀ code ∈ KIP126.LinModule.RawData.Ceta.relations,
      KIP126.LinModule.Presentation.evaluateRelation generatorImage code = 0 := by
  have hblocks : ∀ block ∈ KIP126.LinModule.RawData.Ceta.relationChunks.toList,
      ∀ code ∈ block, KIP126.LinModule.Presentation.evaluateRelation generatorImage code = 0 := by
    change ∀ block ∈ ['''+', '.join(f'KIP126.LinModule.RawData.Ceta.relationChunk{bi}'for bi in range(block_count))+f'''],
      ∀ code ∈ block, KIP126.LinModule.Presentation.evaluateRelation generatorImage code = 0
    simp only [List.forall_mem_cons, List.forall_mem_nil]
    exact ⟨'''+', '.join(f'Relations{bi:03d}.all_relations_zero'for bi in range(block_count))+f''', (by simp)⟩
  intro code hcode
  obtain ⟨block, hblock, hcode⟩ := List.mem_flatten.mp hcode
  exact hblocks block hblock code hcode

/-- A map of the entire fixed native quotient, not an actual spectrum-map comparison. -/
noncomputable def nativeMap : KIP126.LinModule.Ceta.Model →ₗ[E2] E2 :=
  KIP126.LinModule.Presentation.desc generatorImage _ all_relations_zero

theorem nativeMap_generator (i : KIP126.LinModule.Ceta.Generator) :
    nativeMap (KIP126.LinModule.Ceta.generator i) =
      nativeImage (KIP126.LinModule.RawData.Maps.CetaToSphere.imageCode i) :=
  KIP126.LinModule.Presentation.desc_generator generatorImage _ all_relations_zero i

theorem nativeMap_monomial (code : String) :
    nativeMap (KIP126.LinModule.Ceta.monomial code) =
      KIP126.LinModule.Presentation.evaluatePowers generatorImage
        ((code.splitOn ",").map (fun a => a.toNat?.getD 0)) :=
  KIP126.LinModule.Presentation.desc_monomialVector generatorImage _ all_relations_zero code

theorem nativeMap_unique (f : KIP126.LinModule.Ceta.Model →ₗ[E2] E2)
    (h : ∀ i, f (KIP126.LinModule.Ceta.generator i) = generatorImage i) : f = nativeMap :=
  KIP126.LinModule.Presentation.desc_unique generatorImage _ all_relations_zero f h
end {CETA}
''';emit(BASE+'.CetaToSphere.Proofs',text,'final')
 checks=f'''import {BASE}.CetaToSphere.Proofs
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def.StageInput).isPrefixOf mod || mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "native full map imports an actual-model/delivery or basis premise: {{mod}}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``{CETA}.imagePolynomial_evaluate, ``{CETA}.image_zero,
      ``{CETA}.all_relations_zero, ``{CETA}.nativeMap,
      ``{CETA}.nativeMap_generator, ``{CETA}.nativeMap_monomial, ``{CETA}.nativeMap_unique] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected full map axiom: {{decl}}: {{ax}}"
#print axioms {CETA}.all_relations_zero
#print axioms {CETA}.nativeMap
''';emit(BASE+'.CetaToSphere.Checks',checks,'audit')
 names={j['module']for j in jobs}
 for j in jobs:j['dependencies']=[i for i in j['imports']if i in names]
 inputs={str(p.relative_to(root)):sha(p.read_bytes())for p in [root/'lean-toolchain',root/'lake-manifest.json',root/'KIP126/LinProgram/Generated/ModuleMaps/CetaToSphere.lean',root/'KIP126/LinProgram/Generated/Modules/Ceta.lean',root/'KIP126/LinProgram/Generated/E2.lean',support]}
 manifest={'schema':'lin-native-complete-ceta-certificate-build/v2-repository-support','source_root':str(root),'provenance':provenance,'pinned_source_hashes':inputs,'auxiliary_witness':{'path':'witness/CetaToSphere.jsonl','sha256':sha(witness.read_bytes()),'size':witness.stat().st_size},'generator_sha256':sha(pathlib.Path(__file__).read_bytes()),'generation_inputs':{str(p.resolve()):sha(p.read_bytes())for p in [pathlib.Path(__file__),pathlib.Path(__file__).with_name('rebuild-witness.py'),pathlib.Path(__file__).with_name('replay-ceta.py'),*[root/'KIP126/LinProgram/Translate'/name for name in ('lean_module.py','generate-module-presentations.py','generate-module-maps.py','native-contract.py','replay-lowstem.py','check-branch-d2-coordinates.py')]]},'all_relation_count':76569,'source_blocks':block_count,'ring_relation_count':len(used),'sphere_chunks':chunks,'generator_count':887,'native_graph_bound_in_definition':True,'empty_native_image_semantics':'zero','complete_native_quotient_map_certified':False,'actual_model_comparison_certified':False,'certification_status':'generated_unchecked','jobs':jobs}
 outputs['manifest.json']=canonical(manifest);outputs['witness/CetaToSphere.jsonl']=witness.read_bytes();return outputs

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=pathlib.Path,required=True);ap.add_argument('--output-dir',type=pathlib.Path,required=True);ap.add_argument('--witness',type=pathlib.Path,required=True);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 outputs=build(args.root.resolve(),args.output_dir.resolve(),args.witness.resolve())
 for rel,data in outputs.items():
  dest=args.output_dir/rel
  if args.check:require(dest.is_file()and dest.read_bytes()==data,'generated output mismatch: '+rel)
  else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 expected={rel for rel in outputs if rel.endswith('.lean')};actual={str(p.relative_to(args.output_dir))for p in (args.output_dir/'src').rglob('*.lean')};require(actual==expected,'stale or missing generated Lean modules')
 print(('Checked'if args.check else 'Generated')+f' complete Ceta plan: {len(expected)} Lean modules, 887 official images, all 76569 original relations.',flush=True)
if __name__=='__main__':main()
