es = []
for line in open('topo.csv'):
	edge = tuple([int(x) for x in line.split(',')])
	es.append(edge)

n = max( max(e[1],e[2]) for e in es)+1

n_vars = len(es) + n*2


in_vars = [[] for _ in range(n)]
out_vars = [[] for _ in range(n)]
cs = []

for i,s,e,w in es:
	in_vars[e].append(i)
	out_vars[s].append(i)
	cs.append(w)

st,ed,must = open('demand.csv').read().split(',')


st = int(st)
ed = int(ed)
must = [int(x) for x in must.split('|')]


print 'min:',' + '.join(['{} x{}'.format(c,i+1) for i,c in enumerate(cs)])+';'
for i in range(n):
	if in_vars[i]:
		print 'x{}'.format(i+len(es)+1),'=', ' + '.join(['x{}'.format(x+1) for x in in_vars[i]])+';'



for i in range(n):
	if out_vars[i]:
		print 'x{}'.format(i+len(es)+1+n),'=', ' + '.join(['x{}'.format(x+1) for x in out_vars[i]])+';'


for i in range(n):
	if i!=st and i!=ed:
		print 'x{} = x{};'.format(i+len(es)+1,i+len(es)+1+n)


print 'x{} = 0;'.format(st+1 + len(es))
print 'x{} = 1;'.format(st+1 + len(es)+n)


print 'x{} = 1;'.format(ed+1 + len(es))
print 'x{} = 0;'.format(ed+1 + len(es)+n)


for x in must:
	if x!=st and x!=ed:
		print 'x{} = 1;'.format(x+1 + len(es))
		print 'x{} = 1;'.format(x+1 + len(es)+n)


for i in range(n_vars):
	print '0<= x{} <=1'.format(i+1)+';'

print 'int ',','.join('x{}'.format(i+1) for i in range(n_vars))+';'