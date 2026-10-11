#!/usr/bin/env python3
"""Regression checks for rejecting stale or altered proof-output receipts."""
import importlib.util,json,tempfile,unittest,os,sys
from unittest.mock import patch
from pathlib import Path
spec=importlib.util.spec_from_file_location('runner',Path(__file__).with_name('runner.py'))
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
class ResumeBoundary(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.path=Path(self.tmp.name)/'proof.olean';self.path.write_bytes(b'kernel output')
  self.receipt={'schema':r.SCHEMA,'key':'expected','exit_code':0,'olean_sha256':r.digest(self.path)}
 def tearDown(self):self.tmp.cleanup()
 def test_intact_receipt(self):self.assertTrue(r.reusable(self.receipt,'expected',self.path))
 def test_modified_output(self):
  self.path.write_bytes(b'altered');self.assertFalse(r.reusable(self.receipt,'expected',self.path))
 def test_failed_compilation(self):
  self.receipt['exit_code']=1;self.assertFalse(r.reusable(self.receipt,'expected',self.path))
 def test_changed_dependency_key(self):self.assertFalse(r.reusable(self.receipt,'changed',self.path))
 def test_unverified_symlink(self):
  link=self.path.with_name('linked.olean');link.symlink_to(self.path);self.assertFalse(r.reusable(self.receipt,'expected',link))
 def test_missing_output(self):
  self.path.unlink();self.assertFalse(r.reusable(self.receipt,'expected',self.path))
 def test_dependency_change_invalidates_descendants(self):
  jobs={'A':{'sha256':'a','dependencies':[]},'B':{'sha256':'b','dependencies':['A']},'C':{'sha256':'c','dependencies':[]}}
  before=r.job_keys(jobs,'ext','input');jobs['A']['sha256']='changed';after=r.job_keys(jobs,'ext','input')
  self.assertNotEqual(before['A'],after['A']);self.assertNotEqual(before['B'],after['B']);self.assertEqual(before['C'],after['C'])
 def test_changed_external_math_invalidates_all(self):
  jobs={'A':{'sha256':'a','dependencies':[]}}
  self.assertNotEqual(r.job_keys(jobs,'before','input'),r.job_keys(jobs,'after','input'))
 def test_file_changed_during_replay(self):
  old={str(self.path):r.digest(self.path)};self.path.write_bytes(b'new source')
  with self.assertRaises(ValueError):r.verify_files(old)
 def test_cyclic_plan_rejected(self):
  jobs={'A':{'sha256':'a','dependencies':['B']},'B':{'sha256':'b','dependencies':['A']}}
  with self.assertRaises(ValueError):r.job_keys(jobs,'ext','input')
 def test_first_namespace_root_does_not_fall_through(self):
  a=Path(self.tmp.name)/'first';b=Path(self.tmp.name)/'second'
  (a/'KIP126').mkdir(parents=True);(b/'KIP126').mkdir(parents=True)
  (b/'KIP126/Test.olean').write_bytes(b'correct')
  with self.assertRaises(ValueError):r.resolve_module([a,b],'KIP126.Test')
 def overlay_fixture(self):
  root=Path(self.tmp.name);out=root/'out';lib=root/'frozen';src=root/'source.olean'
  src.write_bytes(b'correct');p=lib/'KIP126/Test.olean';p.parent.mkdir(parents=True);p.write_bytes(b'correct')
  q=out/'build/lib/lean/KIP126/Test.olean';q.parent.mkdir(parents=True)
  return out,lib,src,q,{'modules':{'KIP126.Test':{'olean':str(src)}}}
 def test_regular_shadow_rejected(self):
  out,lib,src,q,external=self.overlay_fixture();q.write_bytes(b'wrong')
  with self.assertRaises(ValueError):r.bind_overlay(out,{},external,lib)
 def test_wrong_symlink_rejected(self):
  out,lib,src,q,external=self.overlay_fixture();wrong=src.with_name('wrong.olean');wrong.write_bytes(b'wrong');q.symlink_to(wrong)
  with self.assertRaises(ValueError):r.bind_overlay(out,{},external,lib)
 def test_exact_original_link_migrates_to_frozen_input(self):
  out,lib,src,q,external=self.overlay_fixture();q.symlink_to(src)
  r.bind_overlay(out,{},external,lib);self.assertEqual(q.resolve(),(lib/'KIP126/Test.olean').resolve())
 def test_frozen_copy_does_not_alias_mutable_original(self):
  target=Path(self.tmp.name)/'frozen.olean';expected=r.digest(self.path)
  r.frozen_copy(self.path,target,expected);self.path.write_bytes(b'changed original')
  self.assertEqual(r.digest(target),expected);self.assertFalse(target.is_symlink())
 def test_mutated_frozen_copy_rejected(self):
  target=Path(self.tmp.name)/'frozen.olean';expected=r.digest(self.path)
  r.frozen_copy(self.path,target,expected);target.chmod(0o644);target.write_bytes(b'bad')
  with self.assertRaises(ValueError):r.frozen_copy(self.path,target,expected)
 def test_private_sidecar_wrong_target_rejected(self):
  out,lib,src,q,external=self.overlay_fixture();q.symlink_to(lib/'KIP126/Test.olean')
  side=lib/'KIP126/Test.olean.private';side.write_bytes(b'private')
  external['modules']['KIP126.Test']['artifact_suffixes']=['.olean','.olean.private']
  wrong=src.with_name('wrong.private');wrong.write_bytes(b'wrong')
  (q.parent/'Test.olean.private').symlink_to(wrong)
  with self.assertRaises(ValueError):r.verify_resolution(out/'build/lib/lean',lib,external)
 def test_owned_stale_ir_rejected(self):
  self.path.with_suffix('.ir').write_bytes(b'stale executable code')
  with self.assertRaises(ValueError):r.verify_owned_family(self.path)
 def job_fixture(self):
  output=Path(self.tmp.name)/'job';source_root=output/'frozen-sources';source=source_root/'Fake/C.lean'
  source.parent.mkdir(parents=True);source.write_text('example : True := True.intro\n')
  for part in ['logs','running','receipts']:(output/part).mkdir(parents=True)
  job={'source':'unused','sha256':r.digest(source)}
  library=output/'frozen-library';library.mkdir();external={'modules':{}}
  return output,source_root,job,library,external
 def test_transitive_generated_corruption_stops_before_compiler(self):
  out,sr,job,lib,external=self.job_fixture();a=out/'A.olean';b=out/'B.olean'
  a.write_bytes(b'ancestor');b.write_bytes(b'direct');deps={str(a):r.digest(a),str(b):r.digest(b)}
  a.write_bytes(b'altered ancestor')
  with patch.object(r.subprocess,'Popen') as popen:
   with self.assertRaises(ValueError):r.compile_job('Fake.C',job,'key',Path('/bin/false'),{},out,out,sr,deps,{}, {},lib,external)
   popen.assert_not_called()
  self.assertFalse((out/'receipts/Fake.C.json').exists())
 def test_frozen_change_after_process_never_publishes_receipt(self):
  out,sr,job,lib,external=self.job_fixture();obj=lib/'dep.olean';obj.write_bytes(b'original');expected=r.digest(obj)
  class Process:
   pid=os.getpid();returncode=0
   def poll(self):return 0
  def fake_process(command,**kwargs):
   Path(command[command.index('-o')+1]).write_bytes(b'never accepted as a proof')
   obj.write_bytes(b'changed while command ran');return Process()
  with patch.object(r.subprocess,'Popen',side_effect=fake_process):
   with self.assertRaises(ValueError):r.compile_job('Fake.C',job,'key',Path('/bin/false'),{},out,out,sr,{}, {},{str(obj):expected},lib,external)
  self.assertFalse((out/'receipts/Fake.C.json').exists())
  obj.write_bytes(b'original')
  self.assertFalse((out/'receipts/Fake.C.json').exists())
  pending=out/'build/lib/lean/Fake/C.pending.olean'
  self.assertTrue(pending.exists())
  r.clean_owned_partials(out,{'Fake.C':job})
  self.assertFalse(pending.exists())
  def repaired_process(command,**kwargs):
   Path(command[command.index('-o')+1]).write_bytes(b'isolated test process output')
   return Process()
  with patch.object(r.subprocess,'Popen',side_effect=repaired_process):
   result=r.compile_job('Fake.C',job,'key',Path('/bin/false'),{},out,out,sr,{}, {},{str(obj):expected},lib,external)
  self.assertEqual(result['exit_code'],0)
  receipt=json.loads((out/'receipts/Fake.C.json').read_text())
  self.assertTrue(r.reusable(receipt,'key',out/'build/lib/lean/Fake/C.olean'))
 def test_preflight_failure_replaces_old_complete_and_repeat_stays_failed(self):
  out=Path(self.tmp.name)/'main';out.mkdir();root=out/'root';root.mkdir()
  for rel,data in [('generate.py',b'generator'),('templates/Support.lean',b'support'),('witness/data',b'witness'),('src/Fake/C.lean',b'example : True := True.intro')]:
   p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
  manifest={'source_root':str(root),'pinned_source_hashes':{},
   'auxiliary_witness':{'path':'witness/data','sha256':r.digest(out/'witness/data')},
   'generator_sha256':r.digest(out/'generate.py'),'support_template_sha256':r.digest(out/'templates/Support.lean'),
   'jobs':[{'module':'Fake.C','source':'src/Fake/C.lean','sha256':r.digest(out/'src/Fake/C.lean'),'imports':[],'dependencies':[],'kind':'audit'}]}
  r.atomic(out/'manifest.json',manifest);r.atomic(out/'status.json',{'phase':'complete','complete_native_quotient_map_certified':True})
  for _ in range(2):
   with patch.object(sys,'argv',['runner','--output-dir',str(out)]),patch.object(r,'validate_complete_plan',return_value={'final':'Fake.C','audit':'Fake.C'}),patch.object(r,'refresh_external',side_effect=ValueError('freshness failed')):
    with self.assertRaises(ValueError):r.entrypoint()
   state=json.loads((out/'status.json').read_text());self.assertEqual(state['phase'],'failed');self.assertFalse(state['complete_native_quotient_map_certified'])
if __name__=='__main__':unittest.main()
