import java.util.*;

public class SmartParking {
    static final int INF = Integer.MAX_VALUE / 4;

    // ---------- Graph ----------
    static class Edge { int to, w; Edge(int t, int w) { this.to = t; this.w = w; } }
    static class Graph {
        int n; List<List<Edge>> adj = new ArrayList<>(); List<int[]> edges = new ArrayList<>();
        Graph(int n) { this.n = n; for (int i = 0; i < n; i++) adj.add(new ArrayList<>()); }
        void add(int u, int v, int w) { adj.get(u).add(new Edge(v, w)); adj.get(v).add(new Edge(u, w)); edges.add(new int[]{u, v, w}); }
    }
    static class Lot { int node, cap, free; String name; Lot(String nm, int node, int cap) { name = nm; this.node = node; this.cap = cap; free = cap; } }
    static class Vehicle { String id; int pri, arr; Vehicle(String id, int p, int a) { this.id = id; pri = p; arr = a; } }

    // ---------- Unit IV: graph algorithms ----------
    static int[][] dijkstra(Graph g, int s) {
        int[] d = new int[g.n], p = new int[g.n]; Arrays.fill(d, INF); Arrays.fill(p, -1); d[s] = 0;
        PriorityQueue<int[]> pq = new PriorityQueue<>((a, b) -> a[1] - b[1]); pq.add(new int[]{s, 0});
        while (!pq.isEmpty()) {
            int[] c = pq.poll(); int u = c[0]; if (c[1] > d[u]) continue;
            for (Edge e : g.adj.get(u)) if (d[u] + e.w < d[e.to]) { d[e.to] = d[u] + e.w; p[e.to] = u; pq.add(new int[]{e.to, d[e.to]}); }
        }
        return new int[][]{d, p};
    }
    static int[] bellmanFord(Graph g, int s) {
        int[] d = new int[g.n]; Arrays.fill(d, INF); d[s] = 0;
        for (int i = 0; i < g.n - 1; i++) {
            boolean ch = false;
            for (int[] e : g.edges) {
                if (d[e[0]] + e[2] < d[e[1]]) { d[e[1]] = d[e[0]] + e[2]; ch = true; }
                if (d[e[1]] + e[2] < d[e[0]]) { d[e[0]] = d[e[1]] + e[2]; ch = true; }
            }
            if (!ch) break;
        }
        return d;
    }
    static int[][] floyd(Graph g) {
        int n = g.n; int[][] d = new int[n][n];
        for (int[] r : d) Arrays.fill(r, INF);
        for (int i = 0; i < n; i++) d[i][i] = 0;
        for (int[] e : g.edges) { d[e[0]][e[1]] = Math.min(d[e[0]][e[1]], e[2]); d[e[1]][e[0]] = Math.min(d[e[1]][e[0]], e[2]); }
        for (int k = 0; k < n; k++) for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
            if (d[i][k] + d[k][j] < d[i][j]) d[i][j] = d[i][k] + d[k][j];
        return d;
    }
    static int[] bfs(Graph g, int s) {
        int[] h = new int[g.n]; Arrays.fill(h, -1); h[s] = 0; ArrayDeque<Integer> q = new ArrayDeque<>(); q.add(s);
        while (!q.isEmpty()) { int u = q.poll(); for (Edge e : g.adj.get(u)) if (h[e.to] < 0) { h[e.to] = h[u] + 1; q.add(e.to); } }
        return h;
    }
    static int dfsCount(Graph g, int s) {
        boolean[] seen = new boolean[g.n]; Deque<Integer> st = new ArrayDeque<>(); st.push(s); seen[s] = true; int c = 0;
        while (!st.isEmpty()) { int u = st.pop(); c++; for (Edge e : g.adj.get(u)) if (!seen[e.to]) { seen[e.to] = true; st.push(e.to); } }
        return c;
    }
    static int[] uf;
    static int find(int x) { while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; }
    static int kruskal(Graph g) {
        uf = new int[g.n]; for (int i = 0; i < g.n; i++) uf[i] = i;
        List<int[]> es = new ArrayList<>(g.edges); es.sort((a, b) -> a[2] - b[2]); int t = 0;
        for (int[] e : es) { int a = find(e[0]), b = find(e[1]); if (a != b) { uf[a] = b; t += e[2]; } }
        return t;
    }
    static int prim(Graph g) {
        boolean[] in = new boolean[g.n]; PriorityQueue<int[]> pq = new PriorityQueue<>((a, b) -> a[1] - b[1]); pq.add(new int[]{0, 0}); int t = 0;
        while (!pq.isEmpty()) { int[] c = pq.poll(); if (in[c[0]]) continue; in[c[0]] = true; t += c[1];
            for (Edge e : g.adj.get(c[0])) if (!in[e.to]) pq.add(new int[]{e.to, e.w}); }
        return t;
    }

    // ---------- Unit II: divide & conquer, greedy ----------
    static void mergeSort(Vehicle[] a, int l, int r, Comparator<Vehicle> c) {
        if (r - l < 1) return; int m = (l + r) / 2; mergeSort(a, l, m, c); mergeSort(a, m + 1, r, c);
        Vehicle[] t = new Vehicle[r - l + 1]; int i = l, j = m + 1, k = 0;
        while (i <= m && j <= r) t[k++] = c.compare(a[i], a[j]) <= 0 ? a[i++] : a[j++];
        while (i <= m) t[k++] = a[i++]; while (j <= r) t[k++] = a[j++];
        System.arraycopy(t, 0, a, l, t.length);
    }
    static void mergeSortInt(int[] a, int[] t, int l, int r) {
        if (l >= r) return; int m = (l + r) >>> 1; mergeSortInt(a, t, l, m); mergeSortInt(a, t, m + 1, r);
        int i = l, j = m + 1, k = l; while (i <= m && j <= r) t[k++] = a[i] <= a[j] ? a[i++] : a[j++];
        while (i <= m) t[k++] = a[i++]; while (j <= r) t[k++] = a[j++]; System.arraycopy(t, l, a, l, r - l + 1);
    }
    static Random RND = new Random(7);
    static void quickSort(int[] a, int l, int r) {
        while (l < r) {
            int p = a[l + RND.nextInt(r - l + 1)], i = l, j = r;
            while (i <= j) { while (a[i] < p) i++; while (a[j] > p) j--; if (i <= j) { int x = a[i]; a[i] = a[j]; a[j] = x; i++; j--; } }
            if (j - l < r - i) { quickSort(a, l, j); l = i; } else { quickSort(a, i, r); r = j; }
        }
    }
    static int upperBound(int[] a, int x) { int lo = 0, hi = a.length; while (lo < hi) { int m = (lo + hi) >>> 1; if (a[m] <= x) lo = m + 1; else hi = m; } return lo; }
    static int cmp;
    static int[] maxMin(int[] a, int l, int r) {
        if (l == r) return new int[]{a[l], a[l]};
        if (r == l + 1) { cmp++; return a[l] < a[r] ? new int[]{a[l], a[r]} : new int[]{a[r], a[l]}; }
        int m = (l + r) / 2; int[] x = maxMin(a, l, m), y = maxMin(a, m + 1, r); cmp += 2;
        return new int[]{Math.min(x[0], y[0]), Math.max(x[1], y[1])};
    }
    static int activitySelection(int[][] res) { // {start, finish}
        int[][] s = res.clone(); Arrays.sort(s, (a, b) -> a[1] - b[1]); int c = 0, last = -1;
        for (int[] r : s) if (r[0] >= last) { c++; last = r[1]; } return c;
    }
    static double fractionalKnapsack(double[] w, double[] v, double cap) {
        Integer[] idx = new Integer[w.length]; for (int i = 0; i < idx.length; i++) idx[i] = i;
        Arrays.sort(idx, (a, b) -> Double.compare(v[b] / w[b], v[a] / w[a])); double tot = 0;
        for (int i : idx) { if (cap <= 0) break; double take = Math.min(w[i], cap); tot += take * v[i] / w[i]; cap -= take; } return tot;
    }
    static int jobSequencing(int[][] jobs) { // {deadline, profit}
        int[][] j = jobs.clone(); Arrays.sort(j, (a, b) -> b[1] - a[1]); int md = 0; for (int[] x : j) md = Math.max(md, x[0]);
        boolean[] used = new boolean[md + 1]; int p = 0;
        for (int[] x : j) for (int t = Math.min(md, x[0]); t >= 1; t--) if (!used[t]) { used[t] = true; p += x[1]; break; }
        return p;
    }
    static int[][] strassen(int[][] A, int[][] B) {
        int n = A.length; if (n == 1) return new int[][]{{A[0][0] * B[0][0]}}; int h = n / 2;
        int[][] a11 = blk(A, 0, 0, h), a12 = blk(A, 0, h, h), a21 = blk(A, h, 0, h), a22 = blk(A, h, h, h);
        int[][] b11 = blk(B, 0, 0, h), b12 = blk(B, 0, h, h), b21 = blk(B, h, 0, h), b22 = blk(B, h, h, h);
        int[][] m1 = strassen(add(a11, a22, 1), add(b11, b22, 1)), m2 = strassen(add(a21, a22, 1), b11), m3 = strassen(a11, add(b12, b22, -1)),
                m4 = strassen(a22, add(b21, b11, -1)), m5 = strassen(add(a11, a12, 1), b22), m6 = strassen(add(a21, a11, -1), add(b11, b12, 1)),
                m7 = strassen(add(a12, a22, -1), add(b21, b22, 1));
        int[][] c11 = add(add(m1, m4, 1), add(m7, m5, -1), 1), c12 = add(m3, m5, 1), c21 = add(m2, m4, 1), c22 = add(add(m1, m2, -1), add(m3, m6, 1), 1);
        int[][] C = new int[n][n];
        for (int i = 0; i < h; i++) for (int j = 0; j < h; j++) { C[i][j] = c11[i][j]; C[i][j + h] = c12[i][j]; C[i + h][j] = c21[i][j]; C[i + h][j + h] = c22[i][j]; }
        return C;
    }
    static int[][] blk(int[][] M, int r, int c, int h) { int[][] R = new int[h][h]; for (int i = 0; i < h; i++) for (int j = 0; j < h; j++) R[i][j] = M[r + i][c + j]; return R; }
    static int[][] add(int[][] A, int[][] B, int s) { int n = A.length; int[][] R = new int[n][n]; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) R[i][j] = A[i][j] + s * B[i][j]; return R; }
    static int[][] naive(int[][] A, int[][] B) { int n = A.length; int[][] R = new int[n][n]; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) for (int k = 0; k < n; k++) R[i][j] += A[i][k] * B[k][j]; return R; }

    // ---------- Unit III: dynamic programming ----------
    static int knapBottomUp(int[] w, int[] v, int W) { int[] dp = new int[W + 1]; for (int i = 0; i < w.length; i++) for (int c = W; c >= w[i]; c--) dp[c] = Math.max(dp[c], dp[c - w[i]] + v[i]); return dp[W]; }
    static int[][] memo; static int calls;
    static int knapTopDown(int i, int c, int[] w, int[] v) {
        if (i == w.length || c == 0) return 0; if (memo[i][c] >= 0) return memo[i][c]; calls++;
        int best = knapTopDown(i + 1, c, w, v); if (w[i] <= c) best = Math.max(best, v[i] + knapTopDown(i + 1, c - w[i], w, v)); return memo[i][c] = best;
    }
    static int lcs(String a, String b) {
        int[][] L = new int[a.length() + 1][b.length() + 1];
        for (int i = 1; i <= a.length(); i++) for (int j = 1; j <= b.length(); j++)
            L[i][j] = a.charAt(i - 1) == b.charAt(j - 1) ? L[i - 1][j - 1] + 1 : Math.max(L[i - 1][j], L[i][j - 1]);
        return L[a.length()][b.length()];
    }
    static int[] optimalBST(int[] f) {
        int n = f.length; int[][] c = new int[n + 2][n + 1], root = new int[n + 2][n + 1]; int[] pre = new int[n + 1];
        for (int i = 1; i <= n; i++) pre[i] = pre[i - 1] + f[i - 1];
        for (int i = 1; i <= n; i++) { c[i][i] = f[i - 1]; root[i][i] = i; }
        for (int len = 2; len <= n; len++) for (int i = 1; i + len - 1 <= n; i++) {
            int j = i + len - 1; c[i][j] = INF;
            for (int r = i; r <= j; r++) { int t = (r > i ? c[i][r - 1] : 0) + (r < j ? c[r + 1][j] : 0) + pre[j] - pre[i - 1]; if (t < c[i][j]) { c[i][j] = t; root[i][j] = r; } }
        }
        return new int[]{c[1][n], root[1][n]};
    }

    // ---------- Unit V: TSP patrol route, bin packing feasibility ----------
    static int[][] D; static int best, nodesBT, nodesBB; static int[] minOut;
    static void tspBT(int u, int mask, int cost, int n) {
        nodesBT++; if (mask == (1 << n) - 1) { best = Math.min(best, cost + D[u][0]); return; }
        for (int v = 1; v < n; v++) if ((mask & (1 << v)) == 0) tspBT(v, mask | (1 << v), cost + D[u][v], n);
    }
    static void tspBB(int u, int mask, int cost, int n) {
        nodesBB++; if (mask == (1 << n) - 1) { best = Math.min(best, cost + D[u][0]); return; }
        int lb = cost; for (int v = 0; v < n; v++) if ((mask & (1 << v)) == 0) lb += minOut[v]; if (lb >= best) return;
        for (int v = 1; v < n; v++) if ((mask & (1 << v)) == 0) tspBB(v, mask | (1 << v), cost + D[u][v], n);
    }
    static int tspApprox(int[][] d) { // MST preorder walk (2-approximation, metric TSP)
        int n = d.length; boolean[] in = new boolean[n]; int[] par = new int[n], key = new int[n]; Arrays.fill(key, INF); key[0] = 0; par[0] = -1;
        List<List<Integer>> ch = new ArrayList<>(); for (int i = 0; i < n; i++) ch.add(new ArrayList<>());
        for (int it = 0; it < n; it++) { int u = -1; for (int i = 0; i < n; i++) if (!in[i] && (u < 0 || key[i] < key[u])) u = i; in[u] = true; if (par[u] >= 0) ch.get(par[u]).add(u);
            for (int v = 0; v < n; v++) if (!in[v] && d[u][v] < key[v]) { key[v] = d[u][v]; par[v] = u; } }
        List<Integer> order = new ArrayList<>(); Deque<Integer> st = new ArrayDeque<>(); st.push(0);
        while (!st.isEmpty()) { int u = st.pop(); order.add(u); List<Integer> c = ch.get(u); for (int i = c.size() - 1; i >= 0; i--) st.push(c.get(i)); }
        int t = 0; for (int i = 0; i < n; i++) t += d[order.get(i)][order.get((i + 1) % n)]; return t;
    }
    static boolean canPack(int[] s, int i, int[] rem) {
        if (i == s.length) return true; Set<Integer> tried = new HashSet<>();
        for (int j = 0; j < rem.length; j++) if (rem[j] >= s[i] && tried.add(rem[j])) { rem[j] -= s[i]; if (canPack(s, i + 1, rem)) { rem[j] += s[i]; return true; } rem[j] += s[i]; }
        return false;
    }

    // ---------- Allocation (core of the system) ----------
    static List<String> allocate(Graph g, int entry, List<Lot> lots, Vehicle[] vs, int[] outCount) {
        int[][] dp = dijkstra(g, entry); int[] d = dp[0], par = dp[1];
        Vehicle[] a = vs.clone(); mergeSort(a, 0, a.length - 1, (x, y) -> x.pri != y.pri ? y.pri - x.pri : x.arr - y.arr);
        List<Lot> order = new ArrayList<>(lots); order.sort((x, y) -> d[x.node] != d[y.node] ? d[x.node] - d[y.node] : x.node - y.node);
        List<String> out = new ArrayList<>(); int ok = 0, rej = 0;
        for (Vehicle v : a) {
            Lot pick = null; for (Lot l : order) if (l.free > 0 && d[l.node] < INF) { pick = l; break; }
            if (pick == null) { out.add(String.format("%s (P%d) -> REJECTED (no reachable free slot)", v.id, v.pri)); rej++; continue; }
            pick.free--; ok++; Deque<Integer> path = new ArrayDeque<>(); for (int x = pick.node; x != -1; x = par[x]) path.push(x);
            StringBuilder sb = new StringBuilder(); for (int x : path) { if (sb.length() > 0) sb.append("-"); sb.append(x); }
            out.add(String.format("%s (P%d) -> %s, cost %d, path %s", v.id, v.pri, pick.name, d[pick.node], sb));
        }
        outCount[0] = ok; outCount[1] = rej; return out;
    }
    static Graph sample() {
        Graph g = new Graph(10); int[][] e = {{0,1,4},{0,2,2},{1,2,1},{1,3,5},{2,4,7},{3,4,4},{3,5,3},{3,6,6},{4,7,2},{4,8,5},{5,6,2},{7,8,1},{4,9,9}};
        for (int[] x : e) g.add(x[0], x[1], x[2]); return g;
    }
    static List<Lot> sampleLots(int[] caps) { String[] nm = {"Lot A","Lot B","Lot C","Lot D","Lot E"}; int[] nodes = {5,6,7,8,9}; List<Lot> l = new ArrayList<>(); for (int i = 0; i < 5; i++) l.add(new Lot(nm[i], nodes[i], caps[i])); return l; }
    static Graph randomGraph(int n, int extra, long seed) {
        Random r = new Random(seed); Graph g = new Graph(n); for (int i = 0; i + 1 < n; i++) g.add(i, i + 1, 1 + r.nextInt(20));
        for (int i = 0; i < extra; i++) { int u = r.nextInt(n), v = r.nextInt(n); if (u != v) g.add(u, v, 1 + r.nextInt(20)); } return g;
    }
    static void pr(String s) { System.out.println(s); }
    static double med(Runnable r) { for (int i = 0; i < 5; i++) r.run(); double[] t = new double[9]; for (int i = 0; i < 9; i++) { long a = System.nanoTime(); r.run(); t[i] = (System.nanoTime() - a) / 1e6; } Arrays.sort(t); return t[4]; }

    public static void main(String[] args) {
        int pass = 0;
        // T1
        pr("=== T1: sample network (10 nodes, 13 roads, 5 lots, 8 vehicles) ===");
        Graph g = sample(); int[] cnt = new int[2];
        Vehicle[] vs = {new Vehicle("V1",1,1),new Vehicle("V2",3,2),new Vehicle("V3",2,3),new Vehicle("V4",1,4),new Vehicle("V5",3,5),new Vehicle("V6",1,6),new Vehicle("V7",2,7),new Vehicle("V8",1,8)};
        List<Lot> lots = sampleLots(new int[]{1,2,1,2,1});
        int[] dd = dijkstra(g, 0)[0]; pr("Dijkstra distances from gate: " + Arrays.toString(dd));
        for (String s : allocate(g, 0, lots, vs, cnt)) pr("  " + s);
        pr("  allocated=" + cnt[0] + " rejected=" + cnt[1]); boolean t1 = cnt[0] == 7 && cnt[1] == 1; pr("  T1 " + (t1 ? "PASS" : "FAIL")); if (t1) pass++;
        // T2
        pr("=== T2: capacity exhausted (1 lot, cap 2, 3 vehicles) ===");
        Graph g2 = new Graph(3); g2.add(0,1,3); g2.add(1,2,4); List<Lot> l2 = new ArrayList<>(); l2.add(new Lot("Lot X",2,2));
        Vehicle[] v2 = {new Vehicle("A",1,1),new Vehicle("B",1,2),new Vehicle("C",1,3)};
        for (String s : allocate(g2, 0, l2, v2, cnt)) pr("  " + s); boolean t2 = cnt[0] == 2 && cnt[1] == 1; pr("  T2 " + (t2 ? "PASS" : "FAIL")); if (t2) pass++;
        // T3
        pr("=== T3: priority conflict (1 free slot; regular arrives first, emergency later) ===");
        List<Lot> l3 = new ArrayList<>(); l3.add(new Lot("Lot X",2,1)); Vehicle[] v3 = {new Vehicle("REG",1,1),new Vehicle("EMG",3,2)};
        List<String> o3 = allocate(g2, 0, l3, v3, cnt); for (String s : o3) pr("  " + s); boolean t3 = o3.get(0).startsWith("EMG") && o3.get(0).contains("Lot X"); pr("  T3 " + (t3 ? "PASS" : "FAIL")); if (t3) pass++;
        // T4
        pr("=== T4: unreachable (disconnected) lot ===");
        Graph g4 = new Graph(4); g4.add(0,1,2); g4.add(2,3,1); List<Lot> l4 = new ArrayList<>(); l4.add(new Lot("Lot Y",3,5)); Vehicle[] v4 = {new Vehicle("Q",2,1)};
        List<String> o4 = allocate(g4, 0, l4, v4, cnt); for (String s : o4) pr("  " + s); boolean t4 = cnt[1] == 1; pr("  DFS reachable from gate=" + dfsCount(g4, 0) + " of 4"); pr("  T4 " + (t4 ? "PASS" : "FAIL")); if (t4) pass++;
        // T5
        pr("=== T5: large network (2000 nodes, ~10000 roads, 100 lots x 5, 400 vehicles) ===");
        Graph g5 = randomGraph(2000, 8000, 11); Random r = new Random(3); List<Lot> l5 = new ArrayList<>(); Set<Integer> used = new HashSet<>();
        while (l5.size() < 100) { int nd = 1 + r.nextInt(1999); if (used.add(nd)) l5.add(new Lot("L" + nd, nd, 5)); }
        Vehicle[] v5 = new Vehicle[400]; for (int i = 0; i < 400; i++) v5[i] = new Vehicle("V" + i, 1 + r.nextInt(3), i);
        long t0 = System.nanoTime(); List<String> o5 = allocate(g5, 0, l5, v5, cnt); long t5 = System.nanoTime() - t0;
        int[] dj = dijkstra(g5, 0)[0]; long b0 = System.nanoTime(); int[] bf = bellmanFord(g5, 0); long bt = System.nanoTime() - b0;
        boolean same = Arrays.equals(dj, bf); pr("  allocated=" + cnt[0] + " rejected=" + cnt[1] + " ; Dijkstra==Bellman-Ford: " + same);
        pr(String.format("  allocation time %.2f ms", t5 / 1e6)); boolean tt5 = cnt[0] == 400 && same; pr("  T5 " + (tt5 ? "PASS" : "FAIL")); if (tt5) pass++;
        pr("TESTS PASSED: " + pass + "/5");

        pr("\n=== Unit IV benchmark (median of 9 runs after warm-up, ms) ===");
        for (int n : new int[]{500, 1000, 2000, 4000}) { final Graph b = randomGraph(n, 5 * n, 5);
            pr(String.format("n=%d m=%d  Dijkstra %.3f  Bellman-Ford %.3f", n, b.edges.size(), med(() -> dijkstra(b, 0)), med(() -> bellmanFord(b, 0)))); }
        for (int n : new int[]{100, 200, 300}) { final Graph b = randomGraph(n, 4 * n, 9); final int nn = n;
            pr(String.format("n=%d  Floyd-Warshall %.3f  n x Dijkstra %.3f", n, med(() -> floyd(b)), med(() -> { for (int s0 = 0; s0 < nn; s0++) dijkstra(b, s0); }))); }
        Graph sg = sample(); pr("Sample graph: BFS hops from gate=" + Arrays.toString(bfs(sg, 0)) + " ; DFS reaches " + dfsCount(sg, 0) + " nodes");
        pr("Sample graph: MST (lane network) cost Kruskal=" + kruskal(sg) + " Prim=" + prim(sg));
        int[][] fw = floyd(sg); pr("Floyd-Warshall gate->Lot E=" + fw[0][9] + ", Lot A->Lot E=" + fw[5][9]);

        pr("\n=== Unit II / III modules ===");
        for (int n : new int[]{50000, 100000, 200000}) { final int[] a0 = new Random(1).ints(n, 0, 1000000).toArray(); final int nn = n;
            int[] x = a0.clone(), y = a0.clone(), z = a0.clone(); mergeSortInt(x, new int[n], 0, n - 1); quickSort(y, 0, n - 1); Arrays.sort(z);
            pr(String.format("sort n=%d  merge %.2f  quick %.2f  Arrays.sort %.2f ms  equal=%b", n, med(() -> mergeSortInt(a0.clone(), new int[nn], 0, nn - 1)), med(() -> quickSort(a0.clone(), 0, nn - 1)), med(() -> Arrays.sort(a0.clone())), Arrays.equals(x, y) && Arrays.equals(x, z))); }
        int[] sd = {11, 11, 12, 13, 18}; pr("Binary search: lots within cost 12 = " + upperBound(sd, 12) + ", within 15 = " + upperBound(sd, 15));
        cmp = 0; int[] mm = maxMin(new int[]{11,11,12,13,18,2,7,9}, 0, 7); pr("Max-Min of 8 values: min=" + mm[0] + " max=" + mm[1] + " comparisons=" + cmp + " (3n/2-2=10)");
        pr("Activity selection (reservations): " + activitySelection(new int[][]{{1,4},{3,5},{0,6},{5,7},{3,9},{5,9},{6,10},{8,11},{8,12},{2,14},{12,16}}) + " of 11 reservations");
        pr("Fractional knapsack (EV charging 50 kW): value=" + fractionalKnapsack(new double[]{10,20,30}, new double[]{60,100,120}, 50));
        pr("Job sequencing (deadline,priority): profit=" + jobSequencing(new int[][]{{2,100},{1,19},{2,27},{1,25},{3,15}}));
        int[][] A = new int[8][8]; for (int[] e : sg.edges) { if (e[0] < 8 && e[1] < 8) { A[e[0]][e[1]] = 1; A[e[1]][e[0]] = 1; } }
        pr("Strassen A^2 equals naive A^2 (8x8 adjacency): " + Arrays.deepEquals(strassen(A, A), naive(A, A)));
        int[] w = {2, 4, 1, 2, 3}, val = {6, 9, 3, 5, 7}; memo = new int[w.length][11]; for (int[] x : memo) Arrays.fill(x, -1); calls = 0;
        pr("0/1 knapsack (cap 10) bottom-up=" + knapBottomUp(w, val, 10) + " top-down=" + knapTopDown(0, 10, w, val) + " (subproblems solved=" + calls + ")");
        pr("LCS(TN37AB1234, TN37A81234)=" + lcs("TN37AB1234", "TN37A81234"));
        int[] ob = optimalBST(new int[]{34, 8, 50, 10, 12}); pr("Optimal BST cost=" + ob[0] + " root=key#" + ob[1] + " (keys A..E, freq 34,8,50,10,12)");

        pr("\n=== Unit V: patrol tour (TSP) on shortest-path metric, 10 stops ===");
        Graph tg = randomGraph(10, 14, 21); D = floyd(tg); int n = 10; best = INF; nodesBT = 0; long q0 = System.nanoTime(); tspBT(0, 1, 0, n); long q1 = System.nanoTime(); int optBT = best;
        minOut = new int[n]; for (int i = 0; i < n; i++) { int m = INF; for (int j = 0; j < n; j++) if (i != j) m = Math.min(m, D[i][j]); minOut[i] = m; }
        best = INF; nodesBB = 0; tspBB(0, 1, 0, n); long q2 = System.nanoTime(); int optBB = best; int ap = tspApprox(D);
        pr(String.format("Backtracking opt=%d nodes=%d (%.2f ms) ; Branch&Bound opt=%d nodes=%d (%.2f ms) ; MST 2-approx=%d ratio=%.3f", optBT, nodesBT, (q1 - q0) / 1e6, optBB, nodesBB, (q2 - q1) / 1e6, ap, ap / (double) optBT));
        pr("Bin-packing feasibility sizes [4,3,3,2,2,1] into capacities [6,5,4]: " + canPack(new int[]{4,3,3,2,2,1}, 0, new int[]{6,5,4}));
        pr("Bin-packing feasibility sizes [4,4,4,3] into capacities [6,6]: " + canPack(new int[]{4,4,4,3}, 0, new int[]{6,6}));
    }
}
