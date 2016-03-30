#include <algorithm>
#include <climits>
#include <cstring>
#include <cstdio>
#include <iostream>
#include <cmath>
#define min(x,y) ((x)<(y)?(x):(y))
#define inf 1000000000
using namespace std;
#define N 1000050
#define M 1000050
struct Dinic {
	int s, t, n, pre[N], cur[N], h[N], level[N], sign, q[N];
	int cap[M], to[M], ne[M], flow, e;
	void liu(int u, int v, int w) {
		to[e] = v, ne[e] = h[u], cap[e] = w;
		h[u] = e++;
	}
	void link(int u, int v, int w) {
		liu(u, v, w);
		liu(v, u, 0);
	}
	void init(int n) {
		for (int i = 0; i <= n; ++i)
			h[i] = -1;
		e = 0;
	}
	bool bfs() {
		int L = 0, R = 0;
		fill(level, level + n, -1);
		sign = q[R++] = t;
		level[t] = 0;
		while (L < R && level[s] == -1) {
			int c = q[L++];
			for (int k = h[c]; ~k; k = ne[k]) {
				if (cap[k ^ 1] > 0 && level[to[k]] == -1)
					level[to[k]] = level[c] + 1, q[R++] = to[k];
			}
		}
		return ~level[s];
	}
	void push() {
		int pl = inf, p, k;
		for (p = t; p != s; p = to[k ^ 1]) {
			k = pre[p];
			pl = min(pl, cap[k]);
		}
		for (p = t; p != s; p = to[k ^ 1]) {
			k = pre[p];
			cap[k] -= pl;
			cap[k ^ 1] += pl;
			if (cap[k] == 0)
				sign = to[k ^ 1];
		}
		flow += pl;
	}
	void dfs(int c) {
		if (c == t)
			push();
		else {
			for (int &k = cur[c]; ~k; k = ne[k])
				if (cap[k] > 0 && level[to[k]] + 1 == level[c]) {
					pre[to[k]] = k;
					dfs(to[k]);
					if (level[sign] > level[c])
						return;
					sign = t;
				}
			level[c] = -1;
		}
	}
	int run(int _s, int _t, int _n) {
		s = _s, t = _t, n = _n;
		flow = 0;
		while (bfs()) {
			for (int i = 0; i < n; ++i)
				cur[i] = h[i];
			dfs(s);
		}
		return flow;
	}
} mf;
int r[66], c[66];
int idr[66], idc[66];
int a[66][66];
int main() {
	int tt, i, j, ri = 0;
	scanf("%d", &tt);
	while (tt--) {
		int n, m, s, t;
		int sr, sc;
		sr = sc = 0;
		scanf("%d%d", &n, &m);
		s = n + m, t = s + 1;
		mf.init(t + 2);
		for (i = 0; i < n; ++i) {
			for (j = 0; j < m; ++j) {
				mf.link(i, j + n, 1);
			}
		}
		for (i = 0; i < n; ++i) {
			scanf("%d", &r[i]);
			idr[i] = mf.e;
			mf.link(s, i, r[i]);
			sr += r[i];
		}
		for (i = 0; i < m; ++i) {
			scanf("%d", &c[i]);
			idc[i] = mf.e;
			mf.link(i + n, t, c[i]);
			sc += c[i];
		}
		if (sr != sc) {
			printf("Case %d: impossible\n", ++ri);
			continue;
		}

		int flow = mf.run(s, t, t + 1);
		if (flow != sr) {
			printf("Case %d: impossible\n", ++ri);
			continue;
		}

		for (i = 0; i < n; ++i) {
			for (j = 0; j < m; ++j) {
				int id = i * m + j;
				if (mf.cap[id<<1] == 1) {

					a[i][j] = 0;
					mf.cap[id<<1] = 0;
				} else {
					int id1 = idr[i];
					int id2 = idc[j];
					mf.cap[id1] += 1;
					mf.cap[id1 + 1] -= 1;
					mf.cap[id2] += 1;
					mf.cap[id2 + 1] -= 1;
					int flow = mf.run(s, t, t + 1);
					if (flow == 0) {
						a[i][j] = 1;
						mf.cap[id1]--;
						mf.cap[id2]--;
						mf.cap[id<<1|1]=0;
					} else {
						a[i][j] = 0;
					}
				}

			}
		}
		printf("Case %d:\n", ++ri);
		for (i = 0; i < n; ++i) {
			for (j = 0; j < m; ++j) {
				printf("%d", a[i][j]);
			}
			puts("");
		}
	}

}

        
