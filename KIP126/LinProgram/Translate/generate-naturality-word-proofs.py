#!/usr/bin/env python3
"""Emit transparent proof scripts for the authenticated Words200 certificate.

Run replay-naturality-words.py --check first. This script proposes Lean source;
only compilation of all emitted modules certifies the mathematical equations.
Runtime character extraction in a proposed script is checked by kernel rfl
against the existing unmodified archived chunk, never trusted as a theorem.
"""
import argparse, csv, json
import importlib.util
import io
from pathlib import Path

import sys as _module_sys
from pathlib import Path as _ModulePath
_module_sys.path.insert(0, str(_ModulePath(__file__).resolve().parent))
from lean_module import lean_module, module_output
ROOT = Path(__file__).resolve().parents[3]
LIN = ROOT/'KIP126/LinProgram'
BASE = 'KIP126.LinProgram.Certificates.Naturality.Words200'
NS = 'KIP126.LinModule.NaturalityWords200'
RAW = 'KIP126.LinModule.RawData.NaturalityWords200'
HEADER = '''\n/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/\n'''
OPTIONS = '''set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
  BasisCatalogue.splitOn_pipe
'''
# Relation memberships do not decode basis rows or require the full basis archive.
RELATION_OPTIONS = OPTIONS.replace("  BasisCatalogue.splitOn_pipe\n", "")

def q(s): return json.dumps(s, ensure_ascii=False)
def row(r): return '⟨'+', '.join(map(str,[r['s'],r['t'],r['local_index']]))+', '+q(r['code'])+'⟩'
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    p=json.loads((LIN/'Generated/Naturality/Words200/Manifest.json').read_text())
    out={}
    def emit(name,txt):
        txt = 'import all Init.Data.List.SplitOn.Basic\n' + txt
        out[LIN/('Certificates/Naturality/Words200/'+name+'.lean')]=lean_module(txt)
    relgroups={}
    for i,r in enumerate(p['relation_records']):relgroups.setdefault(r['chunk_index'],[]).append((i,r))
    for ci,records in relgroups.items():
        name='RelationsFirst' if ci is None else f'RelationChunk{ci:03d}'
        parts=[f'import {BASE}.Support\n'+HEADER+f'namespace {NS}.Shared.{name}\nopen KIP126.LinE2 NativeMapCertificates BatchMapCertificate\n'+RELATION_OPTIONS]
        if ci is not None:
            # Small shared lists avoid reducing a thousand-row lookup for each
            # selected relation. Their flattening is still the full old chunk.
            for b in range(32):
                parts.append(f'''open Lean Elab Tactic in
private def block{b} : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[{ci}]!).splitOn "\\n" |>.drop {32*b} |>.take 32 |>.map String.toList))
    replaceMainGoal []
''')
            parts.append('private def blocks : List (List (List Char)) := ['+', '.join(f'block{b}' for b in range(32))+']\n')
            parts.append('private def rows : List (List Char) := blocks.flatten\n')
            parts.append(f'''private theorem chunkBound : {ci} < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[{ci}]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
''')
            for b in sorted({r['chunk_line_index']//32 for _,r in records}):
                parts.append(f'''private theorem block{b}_mem : block{b} ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := {b}) (by decide)
private theorem block{b}_in_rows (r : List Char) (hr : r ∈ block{b}) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block{b}, block{b}_mem, hr⟩
''')
        for i,r in records:
            code=q(r['rel'])
            parts.append(f'theorem relation{i}_mem : {code} ∈ LinE2.RawData.relations := by\n')
            if ci is None:parts.append('  exact List.mem_append_left _ (by simp [LinE2.RawData.firstRelations])\n')
            else:
                b,j=divmod(r['chunk_line_index'],32)
                parts.append(f'''  exact relation_member {ci} chunkBound rows transcription
    (block{b}[{j}]'(by decide)) (block{b}_in_rows _ (List.getElem_mem _)) (by decide +kernel)
''')
            parts.append(f'''theorem relation{i}_zero : nativeImage {code} = 0 := by
  change projection (relationPolynomial {code}) = 0
  exact csv_relation_zero _ relation{i}_mem
''')
        parts.append(f'end {NS}.Shared.{name}\n');emit('Shared/'+name,''.join(parts))
    targets={r['id']:r for e in p['entries'] for r in e['targets']}
    # Propose target rows only after authenticating the original CSV bytes.
    # The Lean proofs still independently bind each row to the existing archive.
    spec = importlib.util.spec_from_file_location('word_proof_batch', LIN/'Translate/replay-naturality-batch.py')
    batch = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(batch)
    _, manifest_bytes, _ = batch.authenticated('KIP126/LinProgram/Raw/manifest.json')
    manifest = batch.load_json(manifest_bytes.decode())
    fixed = [r for r in manifest['files'] if r['path'] == 'S0_AdamsE2_basis.csv']
    batch.require(len(fixed) == 1, 'basis CSV must have one authenticated manifest identity')
    native = batch.load('native-contract.py', 'word_proof_native')
    _, basis_bytes, digest = native.load_lowstem().pinned('S0_AdamsE2_basis.csv')
    batch.require(digest == fixed[0]['sha256'] and len(basis_bytes) == fixed[0]['size'],
                  'basis CSV disagrees with authenticated native manifest')
    basis=list(csv.DictReader(io.StringIO(basis_bytes.decode('utf-16'))))
    bgroup={}
    for i,r in sorted(targets.items()):
        b=basis[i]
        assert r['code']==b['mon'] and r['s']==int(b['s']) and r['t']==int(b['s'])+int(b['stem']) and r['local_index']==int(b['index'])
        bgroup.setdefault(i//1024,[]).append((i,r))
    for ci,records in bgroup.items():
        name=f'BasisChunk{ci:03d}'
        parts=[f'import {BASE}.CatalogueSupport\n'+HEADER+f'namespace {NS}.Shared.{name}\nopen KIP126.LinE2 NativeMapCertificates BatchMapCertificate\n'+OPTIONS]
        parts.append(f'''open Lean Elab Tactic in
private def rows : Array (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.basisChunks[{ci}]!).splitOn "\\n" |>.map String.toList |>.toArray))
    replaceMainGoal []
private theorem chunkBound : {ci} < LinE2.RawData.basisChunks.size := by decide
private theorem transcription : LinE2.RawData.basisChunks[{ci}]'chunkBound =
    String.ofList (joinRows rows.toList) := by rfl
''')
        for bi in range((len(records)+31)//32):
            selected=records[32*bi:32*(bi+1)]
            parts.append(f'private def bindings{bi} : List (Nat × BasisRow) := ['+',\n  '.join('('+str(i%1024)+', '+row(r)+')' for i,r in selected)+']\n')
        # Check one existing 32-row list at a time. Each public row theorem
        # uses the same soundness theorem on its own complete checked list;
        # no flattening forces every certificate into one large cbv proof.
        for bi in range((len(records)+31)//32):
            parts.append(f'private theorem checked{bi} : bindings{bi}.all (basisBindingCheck rows) = true := by cbv\n')
        for j,(i,r) in enumerate(records):
            bi,k=divmod(j,32)
            parts.append(f'''theorem row{i}_mem : ({row(r)} : BasisRow) ∈ basisRows :=
  basisBindings_mem {ci} chunkBound rows transcription bindings{bi} checked{bi}
    (bindings{bi}[{k}]'(by decide)) (List.getElem_mem _)
''')
        parts.append(f'end {NS}.Shared.{name}\n');emit('Shared/'+name,''.join(parts))
    for shard in p['shards']:
        name=shard['name'];es=p['entries'][shard['offset']:shard['offset']+shard['count']]
        ts=sorted({r['id']:r for e in es for r in e['targets']}.items())
        cis=sorted({p['relation_records'][i]['chunk_index'] for i in shard['relation_indices']},key=lambda c:-1 if c is None else c)
        imports=[f'import KIP126.LinProgram.Generated.Naturality.Words200.{name}\n',f'import {BASE}.Support\n']
        for ci in cis:imports.append(f'import {BASE}.Shared.'+('RelationsFirst' if ci is None else f'RelationChunk{ci:03d}')+'\n')
        for ci in sorted({i//1024 for i,r in ts}):imports.append(f'import {BASE}.Shared.BasisChunk{ci:03d}\n')
        parts=imports+[HEADER+f'namespace {NS}.{name}\nopen KIP126.LinE2 NativeMapCertificates BatchMapCertificate\nopen NaturalityMapCertificate (BasisRecord generatorImage)\nopen {RAW}.{name}\n'+OPTIONS]
        extra_simp = ', List.forall_mem_cons' if shard['relation_indices'] else ''
        parts.append('theorem relations_zero : ∀ code ∈ relationCodes, nativeImage code = 0 := by\n  simp only [relationCodes' + extra_simp + ']\n')
        if not cis:parts.append('  simp\n')
        else:
            ls=[]
            for i in shard['relation_indices']:
                ci=p['relation_records'][i]['chunk_index']; n='RelationsFirst' if ci is None else f'RelationChunk{ci:03d}'
                ls.append(f'Shared.{n}.relation{i}_zero')
            parts.append('  exact ⟨'+', '.join(ls)+', by simp⟩\n')
        parts.append('theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv\n')
        parts.append(f"theorem source_ids : entries.map (fun e => e.source.id) = List.range' {shard['offset']+2} {shard['count']} := by cbv\n")
        parts.append('private def targetRows : List BasisRow := ['+',\n  '.join(row(r) for _,r in ts)+']\n')
        parts.append('private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by\n  simp only [targetRows, List.forall_mem_cons]\n')
        ls=[f'Shared.BasisChunk{i//1024:03d}.row{i}_mem' for i,r in ts]
        if ls:parts.append('  exact ⟨'+', '.join(ls)+', by simp⟩\n')
        else:parts.append('  simp\n')
        parts.append('''private def targetCheck (r : BasisRecord) : Bool :=
  targetRows.any (fun b => decide (b.s = r.s ∧ b.t = r.t ∧
    b.index = r.localIndex ∧ b.monomial = r.code))
private theorem targetCheck_sound (r : BasisRecord) (h : targetCheck r = true) :
    basisRow r ∈ basisRows := by
  obtain ⟨b, hb, h⟩ := List.any_eq_true.mp h
  simp only [decide_eq_true_eq] at h
  have he : b = basisRow r := by cases b; cases r; simp_all [basisRow]
  rw [← he]
  exact targetRows_mem b hb
private theorem targets_checked : entries.all (fun e => e.targets.all targetCheck) = true := by cbv
theorem targets_mem (e : Entry) (he : e ∈ entries) (r : BasisRecord) (hr : r ∈ e.targets) :
    basisRow r ∈ basisRows :=
  targetCheck_sound r ((List.all_eq_true.mp ((List.all_eq_true.mp targets_checked) e he)) r hr)
def certificate : CertifiedBatch :=
  ⟨relationCodes, entries, all_checks, relations_zero, targets_mem⟩
''')
        parts.append(f'end {NS}.{name}\n');emit(name,''.join(parts))
    parts=[f'import {BASE}.{s["name"]}\n' for s in p['shards']]
    parts.append(HEADER+f'namespace {NS}\nopen KIP126.LinE2 NativeMapCertificates BatchMapCertificate\nopen NaturalityMapCertificate (BasisRecord generatorImage)\n'+OPTIONS)
    parts.append('def batches : List CertifiedBatch := ['+', '.join(s['name']+'.certificate' for s in p['shards'])+']\n')
    parts.append('''def entries : List Entry := batches.flatMap CertifiedBatch.entries
/-- Every entry of every generated block has a closed native quotient equation. -/
theorem entry_evaluate (e : Entry) (he : e ∈ entries) :
    Presentation.evaluatePowers generatorImage (word e) = targetValue e := by
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp he
  exact b.entry_evaluate e hb
theorem zero_evaluate (e : Entry) (he : e ∈ entries) (hz : e.targets = []) :
    Presentation.evaluatePowers generatorImage (word e) = 0 := by
  rw [entry_evaluate e he]
  simp only [targetValue, hz, List.map_nil, List.sum_nil]
/-- All 76569 original Ceta relations remain required to descend the full module. -/
theorem entry_desc (e : Entry) (he : e ∈ entries)
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation generatorImage code = 0) :
    Presentation.desc generatorImage RawData.Ceta.relations hrel
      (Ceta.monomial e.source.code) = targetValue e := by
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp he
  exact b.entry_desc e hb hrel
theorem target_row_mem (e : Entry) (he : e ∈ entries) (r : BasisRecord) (hr : r ∈ e.targets) :
    basisRow r ∈ basisRows := by
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp he
  exact b.targets_mem e hb r hr
''')
    parts.append(f"theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2 {len(p['entries'])} := by\n")
    parts.append('  simp only [entries, batches, List.flatMap_cons, List.flatMap_nil, List.map_append, List.append_nil, '+', '.join(s['name']+'.certificate' for s in p['shards'])+', '+', '.join(s['name']+'.source_ids' for s in p['shards'])+']\n')
    parts.append("  repeat' rw [List.range'_append_1]\n")
    parts.append(f"theorem entry_count : entries.length = {len(p['entries'])} := by\n  have h := congrArg List.length source_ids\n  simpa only [List.length_map, List.length_range'] using h\n")
    parts.append(f'end {NS}\n');emit('All',''.join(parts))
    for path,txt in out.items():
        if a.check:
            if not path.exists() or path.read_text()!=txt:raise SystemExit('stale proof script: '+str(path))
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(txt)
    print(('checked' if a.check else 'generated'),len(out),'Lean proof modules')
if __name__=='__main__':main()
