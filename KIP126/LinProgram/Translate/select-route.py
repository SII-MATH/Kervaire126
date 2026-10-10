#!/usr/bin/env python3
"""Select Section 7 computational inputs; never certify their topology.

Only read-only, hash-pinned SQLite/CSV inputs. --check compares generated files.
The scope is a proof-local slice plus its coordinate endpoints, not the 49-spectrum
archive. Unknowns remain cycle/boundary bounds. Retained depth-1 trials become
refutation OBLIGATIONS, never positive differential equations. No proof replay.
"""
import argparse, csv, hashlib, importlib.util, json, sqlite3
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('selected', ROOT/'Translate/import-selected.py')
old = importlib.util.module_from_spec(spec); spec.loader.exec_module(old)
HASHES = dict(old.HASHES, **{
 'Cnu_AdamsSS_t200.db':'e1274528151c3391f5e5f4de72f8428a68b5e145a07bb3cc946781efd9bfdbbe',
 'map_AdamsSS_Cnu_to_S0_t200.db':'348873fdbe993aa6b266c34bb4eca6121ab4a44b086a951cb29026a19a0e57f1',
 'ss.json':'a9a623bf7165e62fcf455e454fdf9195237491bf07bd148902e245aa1dba64d8'})
# Editorial selection: whole bidegrees, including empty ones, not just named vectors.
# High-filtration tails in these stems are necessary for "only" and "never hit".
WINDOWS = [('S0',62,63,261), ('S0',122,127,261),
           ('Cnu',125,127,146)]
# The Cnu slice is further limited below to AF<=14 (sources of short hits),
# AF<=19 at stem125 (targets), and AF<=12 at stem127 (earlier boundaries).
ATOMS = [0,1,2,7,9,13,18,51,69,79,80,82,85,89,188,190,251,275,323,
         340,341,352,366,367,368,375,386,387,391,392,393,395,418,424,436,437]
LOG_IDS = [5541,5990,153768,462481,929469,2671068,212838,154545]
TRIAL_IDS = [2047477,2047478,*range(154532,154538)]
NAMES = {
 ('proofs.db/log',5990):'d2_x_125_8', ('proofs.db/log',5541):'d2_h6',
 ('proofs.db/log',153768):'d3_h4_x_109_12',
 ('proofs.db/log',462481):'d3_h0Sq_x_123_13_2',
 ('proofs.db/log',929469):'d3_x_126_4',
 ('proofs.db/log',2671068):'d7_x_123_combination',
 ('proofs.db/log',212838):'d3_cnu_top',
 ('S0_AdamsE2_basis/d2',513):'d2_h0Six_h6',
 ('S0_AdamsE2_basis/d2',2855):'d2_for_P_h2',
 ('S0_AdamsE2_basis/d2',2923):'d2_for_Q_h2_first',
 ('S0_AdamsE2_basis/d2',2926):'d2_for_Q_h2_second',
 ('Cnu_AdamsE2_ss',3872):'d3_cnu_bottom_x_126_8',
 ('Cnu_AdamsE2_ss',3873):'d3_cnu_bottom_x_126_8_2',
 ('S0_AdamsE2_ss',2702):'W_reaches_e6',
 ('S0_AdamsE2_ss',2852):'Y_reaches_e5',
 ('S0_AdamsE2_ss',2433):'X_reaches_e6',
 ('S0_AdamsE2_ss',2569):'V_reaches_e12',
 ('S0_AdamsE2_ss',3080):'T_reaches_e1000',
}
for i in TRIAL_IDS: NAMES['proofs.db/log',i]='refutation_'+str(i)
# Degree pairs: multiplication is performed in the relation quotient, no table.
PAIRS = set()
def pair(s,t,a,b): PAIRS.add((s,t,a,b))
for p in [(1,1,1,1),(2,2,2,2),(4,4,2,2),(1,32,1,32),
          (1,2,1,16),(2,18,12,121),
          (1,64,1,64),(1,16,12,121),(1,2,13,137),(2,2,8,132),
          (2,2,9,134),(1,2,7,128),(1,64,10,69),(1,32,11,102),
          (4,21,9,116),(4,24,4,24),(8,48,8,48),(16,96,9,54),
          (1,1,1,64),(2,65,9,69),(1,32,8,102),(1,64,8,70),
          (2,64,8,70),(6,6,1,64),(1,1,2,64),(1,1,8,70),
          (1,4,8,130),(1,4,11,133),(1,4,12,134),
          (1,1,13,138),(1,4,13,135),(1,4,10,132),
          (2,64,7,70),(1,64,8,70),(2,64,1,1)]: pair(*p)
# Products of the complete local spaces used for indeterminacy and divisibility.
for stem, lo, hi, a, b in [(122,8,12,1,1),(123,8,16,1,1),
 (125,5,13,1,1),(62,0,10,1,1),(124,10,13,1,2),
 (123,8,11,1,2),(122,8,13,1,4)]:
 for s in range(lo,hi+1): pair(a,b,s,s+stem)


def require(p,msg):
 if not p: raise ValueError(msg)
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as source:
  for block in iter(lambda: source.read(1024*1024), b''): h.update(block)
 return h.hexdigest()
def conn(p): return old.connect(p)
def coords(x): return old.indices(x)
def lean_list(xs): return '['+', '.join(map(str,xs))+']'
def quote(x): return json.dumps(x,ensure_ascii=False)
def olean(o): return '.sphere' if o=='S0' else '.nuCofiber'
def main():
 ap=argparse.ArgumentParser(description=__doc__); ap.add_argument('--check',action='store_true')
 ap.add_argument('--raw-dir',type=Path,default=ROOT/'Raw',
   help='directory containing the exact hash-pinned raw inputs (default: ../Raw)')
 args=ap.parse_args(); raw=args.raw_dir; out=ROOT/'Route'
 for n,h in HASHES.items():
  require(digest(raw/n)==h,'hash mismatch: '+n)
 db={o:conn(raw/n) for o,n in [('S0','S0_AdamsSS_t261.db'),('Cnu','Cnu_AdamsSS_t200.db')]}
 log=conn(raw/'proofs.db'); maps=conn(raw/'map_AdamsSS_Cnu_to_S0_t200.db')
 # Reuse the strict sphere CSV/database cross-check, including d2 and local IDs.
 old.import_rows(log,db['S0'],raw,True)
 manifest=json.loads((raw/'ss.json').read_text())
 require(any(x.get('name')=='Cnu__S0' and x.get('sus')==4 and x.get('type')=='top_cell'
             for x in manifest['maps']), 'top-cell map convention changed')
 require(any(x.get('name')=='S0__Cnu' and x.get('factor')==[0,0,0]
             for x in manifest['maps_v2']), 'bottom-cell convention changed')
 bases={}; ss={}; gens={}
 for o,c in db.items():
  bases[o]=defaultdict(list); ss[o]=defaultdict(list)
  gens[o]={r['id']:dict(r) for r in c.execute(f'SELECT * FROM {o}_AdamsE2_generators ORDER BY id')}
  for r in c.execute(f'SELECT * FROM {o}_AdamsE2_basis ORDER BY id'):
   r=dict(r); k=(r['s'],r['t']); r['local_index']=len(bases[o][k]); bases[o][k].append(r)
   ns=list(map(int,r['mon'].split(','))) if r['mon'] else []
   if o=='Cnu':
    require(len(ns)%2==1,'bad module monomial'); m=gens[o][ns[-1]]; ns=ns[:-1]
    deg=[m['s'],m['t']]
   else: deg=[0,0]
   require(len(ns)%2==0,'bad ring monomial')
   for i,e in zip(ns[::2],ns[1::2]):
    require(e>0 and i in gens['S0'],'bad power'); g=gens['S0'][i]
    deg=[deg[0]+e*g['s'],deg[1]+e*g['t']]
   require(tuple(deg)==k,'incorrect monomial degree')
  for r in c.execute(f'SELECT * FROM {o}_AdamsE2_ss ORDER BY id'):
   ss[o][r['s'],r['t']].append(dict(r))
 core=set()
 for o,a,b,tmax in WINDOWS:
  for stem in range(a,b+1):
   cap=({62:10,63:9,122:12,123:17,124:13}.get(stem,tmax-stem)
        if o=='S0' else {125:19,126:14,127:12}[stem])
   for s in range(cap+1): core.add((o,s,s+stem))
 # Named operands and the complete candidate/divisor spaces for product queries.
 degrees=set(core)
 for i in ATOMS:
  g=gens['S0'][i]; degrees.add(('S0',g['s'],g['t']))
 for s,t,a,b in PAIRS:
  degrees.update([('S0',s,t),('S0',a,b),('S0',s+a,t+b)])
 claims=[]
 def resolve(o,s,t,v):
  require(s>=0 and t>=0 and t<=(261 if o=='S0' else 200),'coordinate outside archive')
  require(all(i<len(bases[o][s,t]) for i in v),'bad local coordinate')
  degrees.add((o,s,t))
 def emit(o,kind,r,s,t,x,st,tt,y,origin,record):
  resolve(o,s,t,x)
  if kind in ['equation','refutation']: resolve(o,st,tt,y)
  claims.append(dict(spectrum=o,kind=kind,r=r,s=s,t=t,x=x,ts=st,tt=tt,y=y,origin=origin,record=record))
 for o,s,t in sorted(core):
  for row in ss[o][s,t]:
   lev=row['level']; x=coords(row['base']); d=row['diff']
   if lev==9000: emit(o,'reaches',1000,s,t,x,s,t,[],o+'_AdamsE2_ss',row)
   elif 9000<lev<=9998:
    r=10000-lev
    if d is None or d in ['-1','[NULL]']: emit(o,'reaches',r,s,t,x,s,t,[],o+'_AdamsE2_ss',row)
    else: emit(o,'equation',r,s,t,x,s+r,t+r-1,coords(d),o+'_AdamsE2_ss',row)
   elif 2<=lev<999:
    if d is None or d in ['-1','[NULL]']: emit(o,'boundaryBy',lev,s,t,x,s,t,[],o+'_AdamsE2_ss',row)
    else: emit(o,'equation',lev,s-lev,t-lev+1,coords(d),s,t,x,o+'_AdamsE2_ss',row)
   else: raise ValueError('unsupported staircase level')
 for i in LOG_IDS+TRIAL_IDS:
  row=dict(log.execute('SELECT * FROM log WHERE id=?',(i,)).fetchone())
  trial=i in TRIAL_IDS
  require(row['depth']==(1 if trial else 0),'unexpected branch context')
  require(row['reason'] in ({'T'} if trial else {'d2','D','N'}),'wrong reason')
  if trial: require(bool(row['info']) and 'However,' in row['info'],
                    'retained trial lacks checked contradiction text')
  r,s,t=row['r'],row['s'],row['t']; require(2<=r<999,'not a finite differential')
  emit(row['name'],'refutation' if trial else 'equation',r,s,t,coords(row['x']),s+r,t+r-1,
       coords(row['dx']),'proofs.db/log',row)
 # CSV/table-only d2; three rows provide the P h2 / Q h2 boundary equations.
 for s,t,mon in [(7,70,'0,6,69,1'),(10,136,'419,1'),(11,137,'427,1'),(11,137,'0,1,419,1')]:
  rs=[x for x in bases['S0'][s,t] if x['mon']==mon]; require(len(rs)==1,'missing d2 basis row')
  row=rs[0]; emit('S0','equation',2,s,t,[row['local_index']],s+2,t+1,coords(row['d2']),
                  'S0_AdamsE2_basis/d2',row)
 # Canonical bottom inclusion: module-generator 0, selected named operands only.
 bottoms=[]
 for s,t,mon in [(8,134,'392,1'),(8,134,'393,1'),(11,136,'0,2,391,1'),(14,139,'1,1,7,1,275,1')]:
  x=[z for z in bases['S0'][s,t] if z['mon']==mon]
  y=[z for z in bases['Cnu'][s,t] if z['mon']==mon+',0']
  require(len(x)==len(y)==1,'bottom image requires reduction, not a direct basis entry')
  resolve('S0',s,t,[x[0]['local_index']]); resolve('Cnu',s,t,[y[0]['local_index']])
  bottoms.append(dict(s=s,t=t,x=[x[0]['local_index']],y=[y[0]['local_index']],source=x[0],target=y[0]))
 # Top lift x_121_7 * (h1[4]); both actual generator image and bidegree checked.
 top=next(z for z in bases['Cnu'][8,134] if z['mon']=='323,1,1')
 m=dict(maps.execute('SELECT * FROM map_AdamsE2_Cnu_to_S0 WHERE id=1').fetchone())
 require(m['map']=='1,1','unexpected top map')
 top_target=next(z for z in bases['S0'][8,130] if z['mon']=='1,1,323,1')
 require(top['local_index']==top_target['local_index']==0,
         'TopCorrect fixed local indices require review')
 resolve('Cnu',8,134,[top['local_index']]); resolve('S0',8,130,[top_target['local_index']])
 ds=[]
 for o,s,t in sorted(degrees):
  ds.append(dict(spectrum=o,s=s,t=t,core=(o,s,t) in core,basis=bases[o][s,t]))
 paper=ROOT.parents[1]/'MainPaper/main.tex'
 data=dict(version=1,dataset='Zenodo 14875701 / v126.3.cw49',sha256=HASHES,
  paper=dict(path='MainPaper/main.tex',
             sha256=hashlib.sha256(paper.read_bytes()).hexdigest(),section='7 and Appendix'),
  scope='Section 7 local inputs; core windows plus coordinate/product endpoints. No proof replay.',
  degrees=ds,claims=claims,products=[dict(s=s,t=t,sp=a,tp=b) for s,t,a,b in sorted(PAIRS)],
  bottom_maps=bottoms,top_map=dict(source=top,target=top_target,generator_image=m),
  named_generators=[gens['S0'][i] for i in ATOMS])
 # Computational integrity: each selected SS staircase is an F2 basis of E2,
 # including all combinations; this is NOT a proof it is the actual SS flag.
 for o,s,t in sorted(core):
  rows=ss[o][s,t]; pivots={}
  for z in rows:
   v=sum(1<<i for i in coords(z['base']))
   while v:
    k=v.bit_length()-1
    if k not in pivots: pivots[k]=v; break
    v^=pivots[k]
   require(v!=0,'dependent staircase vector')
  require(len(pivots)==len(bases[o][s,t]),'staircase not a complete local basis')
 lines=['import KIP126.LinProgram.Route.Raw', '',
 '/-! GENERATED by Translate/select-route.py. Syntax only; no mathematical axiom. -/',
 'namespace KIP126.Computation.Route.Raw', '', 'def degrees : List Degree := [']
 lines+=['  ⟨'+olean(d['spectrum'])+f", {d['s']}, {d['t']}, "+lean_list([quote(x['mon']) for x in d['basis']])+'⟩'+(',' if j<len(ds)-1 else '') for j,d in enumerate(ds)]
 lines+= [']','','def claims : List Claim := [']
 def literal(c):
  return '⟨'+olean(c['spectrum'])+', .'+c['kind']+f", {c['r']}, {c['s']}, {c['t']}, "+lean_list(c['x'])+f", {c['ts']}, {c['tt']}, "+lean_list(c['y'])+', '+quote(c['origin'])+f", {c['record']['id']}⟩"
 for j,c in enumerate(claims):
  lines.append('  '+literal(c)+(',' if j<len(claims)-1 else ''))
 lines+=[']','','def products : List Product := [']
 lines+=['  ⟨'+', '.join(map(str,p))+'⟩'+(',' if j<len(PAIRS)-1 else '') for j,p in enumerate(sorted(PAIRS))]
 lines+=[']','','def bottomMaps : List BottomMap := [']
 lines+=['  ⟨'+f"{p['s']}, {p['t']}, "+lean_list(p['x'])+', '+lean_list(p['y'])+'⟩'+(',' if j<len(bottoms)-1 else '') for j,p in enumerate(bottoms)]
 lines += [']','','end KIP126.Computation.Route.Raw','']
 records=['import KIP126.Interface.Challenge.Challenge2', '',
 '/-! GENERATED named projections from explicit C(M) hypotheses. These theorems',
 'do NOT prove the database computations or add mathematical assumptions. -/',
 'namespace KIP126.Computation.Route',
 'open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams',
 'open KIP126.Synthetic.Context KIP126.Kervaire.Route',
 'universe u v w',
 'variable {C : Type u} [StableHomotopyCategory.{u, v} C]',
 '  [HasFunctorialCofiber (C := C)]',
 '  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]',
 '  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}',
 '  {D : Model H M Syn} {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}',
 'set_option maxRecDepth 10000', '']
 for offset,c in enumerate(claims):
  key=(c['origin'],c['record']['id'])
  if key in NAMES:
   n=NAMES[key]
   records += [f'/-- {key[0]} row {key[1]}; {c["kind"]}. Coordinates are degree-local. -/',
     f'def record_{n} : Raw.Claim := '+literal(c),
     f'theorem Inputs.{n} (I : Inputs D L G) : Statement I.realization record_{n} :=',
     f'  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := {offset}) (by decide))', '']
 records+=['end KIP126.Computation.Route','']
 artifacts={'selected.json':json.dumps(data,ensure_ascii=False,indent=2)+'\n',
            'Selected.lean':'\n'.join(lines),'Records.lean':'\n'.join(records)}
 for n,text in artifacts.items():
  path = (ROOT.parent / 'Main/Solution/Computation/LinProgram/Route' / n) if n == 'Records.lean' else out / n
  if args.check: require(path.read_text()==text,'stale generated file: '+str(path))
  else:
   path.parent.mkdir(parents=True,exist_ok=True)
   path.write_text(text)
 print(json.dumps({'degrees':len(ds),'basis_vectors':sum(len(d['basis']) for d in ds),
    'claims':len(claims),'core_rows':sum(len(ss[o][s,t]) for o,s,t in core),
    'product_degree_pairs':len(PAIRS),'bottom_maps':len(bottoms),'refutations':len(TRIAL_IDS),
    'check':args.check},indent=2))
if __name__=='__main__': main()
