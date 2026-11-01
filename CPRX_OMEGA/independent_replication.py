import json, math, pathlib, csv
p=pathlib.Path(__file__).parent
j=json.loads((p/'FINITE_RING_TESTS/actual_results.json').read_text())
assert j['group_order']==24 and j['center_order']==2
assert j['conjugacy_class_count']==9
assert j['test_count']==j['passed']==46
members={(a,b) for a in (-1,1) for b in range(12)}
assert len(members)==24
comp=lambda x,y:(x[0]*y[0],(x[0]*y[1]+x[1])%12)
assert all(comp(u,v) in members for u in members for v in members)
center=[u for u in members if all(comp(u,v)==comp(v,u) for v in members)]
assert set(center)=={(1,0),(1,6)}
obs=json.loads((p/'vortex_test_results.json').read_text())
with open(p/'VORTEX_MEASUREMENTS.tsv') as f:
 r=csv.DictReader(f,delimiter='\t'); data=[[0]*12 for i in range(6)]
 for row in r:data[int(row['radial_band'])][int(row['sector'])]=float(row['gradient_energy'])
def corr(a,b):
 ma=sum(a)/12;mb=sum(b)/12
 num=sum((x-ma)*(y-mb) for x,y in zip(a,b))
 d=math.sqrt(sum((x-ma)**2 for x in a)*sum((y-mb)**2 for y in b))
 return num/d if d else 0
shift=obs['train_selected_shift']
res=[]
for i in range(2,5):
 rolled=[data[i+1][(j-shift)%12] for j in range(12)]
 res.append(corr(data[i],rolled))
assert max(abs(a-b) for a,b in zip(res,obs['heldout_correlations']))<2e-6
print(json.dumps({'replicated_ring_order':24,'replicated_group_center':center,'replicated_vortex_holdout':res,'max_deviation':max(abs(a-b) for a,b in zip(res,obs['heldout_correlations'])),'status':'PASS'},indent=2))
