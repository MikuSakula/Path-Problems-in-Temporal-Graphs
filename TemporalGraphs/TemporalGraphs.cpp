#include <iostream>
#include <cstring>
#include <cstdio>
#include <algorithm>
#include <vector>
#include <set>
#include <queue>
#include <map>
#include <stack>
#include <cmath>
#include <ctime>
#include <cstdlib>
#include <functional>
#include <string>
#include <utility>
#include <fstream>
#include <afx.h>
using namespace std;
typedef long long ll;
const ll INF = 0x7fffffff;
const int MAXN = 40001;
struct node {  //   定义边信息结构体
	ll time, last;
};
struct cat {  //  定义L列表结构体
	ll s, a;
	cat(ll x, ll y) {    //		构造函数
		s = x, a = y;
	}
	bool operator < (const cat b)const {   //  重载运算符
		return a > b.a;
	}
};
struct qnode {                    //	Dijkstra算法结构体
	int v, c;
	qnode(int _v = 0, int _c = 0) :v(_v), c(_c) {}
	bool operator <(const qnode& r)const {
		return c > r.c;
	}
};
struct Edge {	//		定义边结构体
	int v;
	ll cost;
	Edge(int _v = 0, int _cost = 0) :
		v(_v), cost(_cost) {}
};
vector<Edge>E[MAXN];  //	用于单源最短路边的结构体
bool vis[MAXN];		//	    定义标记数组
int dist[MAXN];		//	    用于存储单源最短路
vector<int>mp[40001];//     存储地图
pair<pair<int, int>, int>pr[90001];     //  使用一个pair对来记录u到v的边 考虑到有重边 我们再加入一个id来防止覆盖
map<pair<pair<int, int>, int>, node>m;   //   我们使用一个核心算法为红黑树的map来映射边 通过调用边结构体来快速找到这条边的信息
map<int, ll>edge;
bool operator < (const pair<pair<int, int>, int>& x, const pair<pair<int, int>, int>& y)
{
	return x.second < y.second;   // map对于键值字典序排序需要重载
}
bool cmp(pair<pair<int, int>, int>x, pair<pair<int, int>, int>y)     //   按照出发时间升序排序
{
	return m[x].time < m[y].time;
}
ll Ta, Tw;   //		定义时间区间
int u, v, loc, n, st;   //  变量的准备工作
ll x, y;
ll t1[40001], t2[40001], f1[40001], f2[40001], d[40001];
void addedge(int u, int v, int w) {
	E[u].push_back(Edge(v, w));
}
void earliest_arrival_time()    //  最早出发时间/路径
{
	t1[st] = Ta;
	for (int i = 0; i < 40001; ++i)
		if (st != i)
			t1[i] = INF;
	for (int i = 0; i < loc; ++i)
		if (m[pr[i]].time + m[pr[i]].last <= Tw && m[pr[i]].time >= t1[pr[i].first.first])
			if (m[pr[i]].time + m[pr[i]].last < t1[pr[i].first.second])
				t1[pr[i].first.second] = m[pr[i]].time + m[pr[i]].last;
	return;
}
void latest_departure_time()     //  最晚出发时间/路径
{
	t2[st] = Tw;
	for (int i = 0; i < 40001; ++i)
		if (st != i)
			t2[i] = -INF;
	for (int i = 0; i < loc; ++i)
	{
		if (m[pr[i]].time >= Ta)
			if (m[pr[i]].time + m[pr[i]].last <= t2[pr[i].first.second])
				if (m[pr[i]].time > t2[pr[i].first.first])
					t2[pr[i].first.first] = m[pr[i]].time;
	}
	return;
}
void fastest_path_duration_multi()    //     最快路径多次通过
{
	f1[st] = 0;
	for (int i = 0; i < 40001; ++i)
		if (st != i)
			f1[i] = INF;
	for (int i = 0; i < loc; ++i)
		//	write<<m[pr[i]].time<<" "<<m[pr[i]].last+m[pr[i]].time<<endl;
		if (m[pr[i]].time >= Ta && m[pr[i]].last + m[pr[i]].time <= Tw)
			if (t1[pr[i].first.second] != INF)
				f1[pr[i].first.second] = abs(min(f1[pr[i].first.second], t1[pr[i].first.second] - m[pr[i]].time));
	return;
}
void fastest_path_duration_onepass()   //	最快路径单次通过
{
	set<cat>q[40001];
	f2[st] = 0;
	for (int i = 0; i < 40001; ++i)
		if (st != i)
			f1[i] = INF;
	for (int i = 0; i < loc; ++i)
	{
		if (m[pr[i]].time >= Ta && m[pr[i]].time + m[pr[i]].last <= Tw)
		{
			if (pr[i].first.first == st)
				if (q[pr[i].first.first].find(cat(m[pr[i]].time, m[pr[i]].time)) == q[pr[i].first.first].end())
					q[pr[i].first.first].insert(cat(m[pr[i]].time, m[pr[i]].time));
			set<cat>::iterator it = q[pr[i].first.first].begin();
			for (; it != q[pr[i].first.first].end(); ++it)
				if ((*it).a <= m[pr[i]].time)
					break;
			cat tt(0, 0);
			if (!q[pr[i].first.first].empty())
				tt.s = (*it).s, tt.a = m[pr[i]].time + m[pr[i]].last;
			else
				tt.s = edge[u], tt.a = m[pr[i]].time + m[pr[i]].last;
			q[pr[i].first.second].insert(tt);
			if (tt.a - tt.s < f2[pr[i].first.second])
				f2[pr[i].first.second] = abs(tt.a - tt.s);
		}
	}
	return;
}
void shortest_path_distance()       //   最短路径
{
	set<cat>q[40001];
	d[st] = 0;
	for (int i = 0; i < 40001; ++i)
		if (st != i)
			d[i] = INF;
	for (int i = 0; i < loc; ++i)
	{
		if (m[pr[i]].time >= Ta && m[pr[i]].time + m[pr[i]].last <= Tw)
		{
			if (pr[i].first.first == st)
				if (q[pr[i].first.first].find(cat(m[pr[i]].time, m[pr[i]].time)) == q[pr[i].first.first].end())
					q[pr[i].first.first].insert(cat(0, m[pr[i]].time));
			set<cat>::iterator it = q[pr[i].first.first].begin();
			for (; it != q[pr[i].first.first].end(); ++it)
				if ((*it).a <= m[pr[i]].time)
					break;
			cat tt(0, 0);
			if (!q[pr[i].first.first].empty())
				tt.s = (*it).s + m[pr[i]].last, tt.a = m[pr[i]].time + m[pr[i]].last;
			else
				tt.s = edge[u] + 1, tt.a == m[pr[i]].time + m[pr[i]].last;
			q[pr[i].first.second].insert(tt);
			if (tt.s - tt.a < d[pr[i].first.second])
				d[pr[i].first.second] = tt.s;
		}
	}
	return;
}
void Dijkstra(int n, int start)     //    采用堆优化的Dijkstra 算法  复杂度nlogn
{
	for (int i = 1; i <= n; i++)
		dist[i] = INF;
	priority_queue<qnode>que;
	dist[start] = 0;
	que.push(qnode(start, 0));
	qnode tmp;
	while (!que.empty())
	{
		tmp = que.top();
		que.pop();
		int u = tmp.v;
		if (vis[u])
			continue;
		vis[u] = true;
		for (int i = 0; i < E[u].size(); i++)
		{
			int v = E[tmp.v][i].v;
			int cost = E[u][i].cost;
			if (!vis[v] && dist[v] > dist[u] + cost)
			{
				dist[v] = dist[u] + cost;
				que.push(qnode(v, dist[v]));
			}
		}
	}
	return;
}
int main()
{
	SetConsoleTitle("时序图最短路");
	// *********************************************************
	if (MessageBox(NULL, "   点确定开始   ", "时序图最短路", MB_OKCANCEL) == 1)    //   消息框设置
		MessageBox(NULL, "   算法开始   ", "时序图最短路", MB_OK);
	else
	{
		MessageBox(NULL, "   键入错误   ", "时序图最短路", MB_OK);
		return 0;
	}
	std::ios::sync_with_stdio(0);
	ifstream read("out.txt");      //    从文件读入
	ofstream write;
	write.open("write.txt");
	if (read.eof())
	{
		cout << "Read Failure!" << endl;
		exit(0);
	}
	while (read >> u >> v >> x >> y)
	{
		mp[u].push_back(v);
		addedge(u, v, x);
		if (!edge[u])
			edge[u] = x;
		else
			edge[u] = min(edge[u], x);
		pr[loc].first.first = u;
		pr[loc].first.second = v;
		pr[loc].second = loc;
		m[pr[loc]].time = x;
		m[pr[loc]].last = y;
		loc++;
	}
	sort(pr, pr + n, cmp);
	read.close();
	printf("输入时间区间\n");
	printf("起始时间:");
	scanf("%lld", &Ta);
	printf("结束时间:");
	scanf("%lld", &Tw);
	printf("输入测试源节点\n节点:");
	scanf("%d", &st);
	if (mp[st].size() == 0) {
		MessageBox(NULL, "   不存在该源节点！   ", "时序图最短路", MB_OK);
		return 0;
	}
	double a, b;
	//   earliest_arrival_time
	a = clock();
	earliest_arrival_time();
	b = clock();
	CString str1 = "   Earliest_arrival_time路径计算完成 耗时   ", str2 = "毫秒";
	CString num;
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Earliest_arrival_time路径计算完成 耗时%.2f毫秒\n", b - a);

	//    latest_departure_time
	a = clock();
	latest_departure_time();
	b = clock();
	str1 = "   Latest_departure_time路径计算完成 耗时 ", str2 = "毫秒";
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Latest_departure_time路径计算完成 耗时%.2f毫秒\n", b - a);
	//    fastest_path_duration_multi
	a = clock();
	fastest_path_duration_multi();
	b = clock();
	str1 = "   Fastest_path_duration_multi路径计算完成 耗时 ", str2 = "毫秒";
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Fastest_path_duration_multi路径计算完成 耗时%.2f毫秒\n", b - a);

	//    fastest_path_duration_onepass
	a = clock();
	fastest_path_duration_onepass();
	b = clock();
	str1 = "   Fastest_path_duration_onepass路径计算完成 耗时 ", str2 = "毫秒";
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Fastest_path_duration_onepass路径计算完成 耗时%.2f毫秒\n", b - a);
	//    shortest_path_distance
	a = clock();
	shortest_path_distance();
	b = clock();
	str1 = "   Shortest_path_distance路径计算完成 耗时 ", str2 = "毫秒";
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Shortest_path_distance路径计算完成 耗时%.2f毫秒\n", b - a);
	//write<<endl;
	printf("\n若假定输入规则为u，v，w\n表示从u到v有一条有向边\n使用堆优化的Dijkstra算法进行计算并输出最短路\n");
	a = clock();
	Dijkstra(40001, st);
	b = clock();
	str1 = "   Dijkstra路径计算完成 耗时 ", str2 = "毫秒";
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("\nDijkstra路径计算完成 耗时%.2f毫秒\n", b - a);
	for (int i = 0; i < 40001; ++i)
		if (t1[i] != INF)
			write << "点" << st << "到" << i << "的最早出发时间是" << t1[i] << endl;
	for (int i = 0; i < 40001; ++i)
		if (t2[i] != -INF && t2[i] != 1)
			write << "点" << st << "到" << i << "的最晚出发时间是" << t2[i] << endl;
	for (int i = 0; i < 40001; ++i)
		if (f1[i] != INF)
			write << "点" << st << "到" << i << "的最快多次通过路径是" << f1[i] << endl;
	for (int i = 0; i < 40001; ++i)
		if (f2[i] != INF && f2[i] != 0)
			write << "点" << st << "到" << i << "的最快单次通过路径是" << f2[i] << endl;
	for (int i = 0; i < 40001; ++i)
		if (d[i] != INF && d[i] != 0)
			write << "点" << st << "到" << i << "的最短路径是" << d[i] << endl;
	write << "以下为静态图的单源最短路" << endl;


	for (int i = 1; i <= 40001; ++i)
		if (dist[i] != INF)
			write << "点" << st << "到" << i << "的单源最短路是" << dist[i] << endl;
	write.close();
	printf("---------------------------------------------------------\n");
	printf("为更直观的观察效率，我们随机制造10个散点进行测试\n");
	double sum1, sum2, sum3, sum4, sum5, sum6;
	srand(time(NULL));
	int rnd[10];
	for (int i = 0; i < 10; ++i)
		rnd[i] = (rand() % 40001 + 7771) % 40001;

	a = clock();
	for (int i = 0; i < 10; ++i) {
		memset(t1, 0, sizeof(t1));
		st = rnd[i];
		earliest_arrival_time();
	}
	b = clock();
	str1 = "   Earliest_arrival_time路径计算10次完成 耗时   ", str2 = "毫秒";
	sum1 = b - a;
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Earliest_arrival_time路径计算10次完成 耗时%.2f毫秒\n", b - a);

	a = clock();
	for (int i = 0; i < 10; ++i) {
		memset(t2, 0, sizeof(t2));
		st = rnd[i];
		latest_departure_time();
	}
	b = clock();
	str1 = "   Latest_departure_time路径计算10次完成 耗时   ", str2 = "毫秒";
	sum2 = b - a;
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Latest_departure_time路径计算10次完成 耗时%.2f毫秒\n", b - a);

	a = clock();
	for (int i = 0; i < 10; ++i) {
		memset(f1, 0, sizeof(f1));
		st = rnd[i];
		fastest_path_duration_multi();
	}
	b = clock();
	str1 = "   Fastest_path_duration_multi路径计算10次完成 耗时   ", str2 = "毫秒";
	num.Format("%.2f", b - a);
	sum3 = b - a;
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Fastest_path_duration_multi路径计算10次完成 耗时%.2f毫秒\n", b - a);

	a = clock();
	for (int i = 0; i < 10; ++i) {
		memset(f2, 0, sizeof(f2));
		st = rnd[i];
		fastest_path_duration_onepass();
	}
	b = clock();
	str1 = "   Fastest_path_duration_onepass路径计算10次完成 耗时   ", str2 = "毫秒";
	sum4 = b - a;
	num.Format("%.2f", b - a);
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Fastest_path_duration_onepass路径计算10次完成 耗时%.2f毫秒\n", b - a);

	a = clock();
	for (int i = 0; i < 10; ++i) {
		memset(d, 0, sizeof(d));
		st = rnd[i];
		shortest_path_distance();
	}
	b = clock();
	str1 = "   Shortest_path_distance路径计算10次完成 耗时   ", str2 = "毫秒";
	num.Format("%.2f", b - a);
	sum5 = b - a;
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("Shortest_path_distance路径计算10次完成 耗时%.2f毫秒\n", b - a);


	a = clock();
	for (int i = 0; i < 10; ++i) {
		memset(vis, 0, sizeof(vis));
		memset(dist, 0, sizeof(dist));
		st = rnd[i];
		Dijkstra(40001, st);
	}
	b = clock();
	str1 = "   Dijkstra路径计算10次完成 耗时 ", str2 = "毫秒";
	num.Format("%.2f", b - a);
	sum6 = b - a;
	MessageBox(NULL, str1 + num + str2, "时序图最短路", MB_OK);
	printf("\nDijkstra路径计算10次完成 耗时%.2f毫秒\n", b - a);
	printf("---------------------------------------------------------\n");
	printf("  算法名称              运行时间         与Dijkstra算法效率相比\n");
	printf("最早出发路径           %7.2f                 %.2f%%\n", sum1, sum6 / sum1 * 100);
	printf("最晚出发路径           %7.2f                %.2f%%\n", sum2, sum6 / sum2 * 100);
	printf("最快路径多次通过       %7.2f                %.2f%%\n", sum3, sum6 / sum3 * 100);
	printf("最快路径单次通过       %7.2f                %.2f%%\n", sum4, sum6 / sum4 * 100);
	printf("最短路径               %7.2f                %.2f%%\n", sum5, sum6 / sum5 * 100);
	printf("综上所述，动态的时序图最短路算法比传统静态图最短路算法更优\n");
	MessageBox(NULL, "   运行成功，算法结束！   ", "时序图最短路", MB_OK);
	return 0;
}
