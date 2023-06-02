#include <iostream>
#include <string>
#include <vector>
#include <cstdlib>
#include <bits/stdc++.h>
#include<random>
#include<chrono>
using namespace std;
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
struct Move {
    int x;
    int y;
    Move operator+(const Move& oth) const {
        return { x + oth.x, y + oth.y };
    }
};

const double MCTS_C = 0.7;
const Move BASIC_DIRECTION[6] = { {-1, 0}, {-1, 1}, {0, 1}, {1, 0}, {1, -1}, {0, -1} };
const int INF = 0x3f3f3f3f;
const int MIN_SIMULATE = 5;
const int MAX_SIMULATE = 10;
const int TIMES_SIMULATE = 5;
const int SIZE = 11;
const int TIMELIMIT = 950 * 10;
const int LAYER = 2;
const int Red = 1;
const int Blue = -1;
const bool USE_JUDGE = true;

struct mcts_node {
    Move node_move;
    mcts_node* parent = nullptr;
    int to_player;
    int visit = 0;
    int value = 0;
    bool isend = false;
    int depth = 0; // test
    int winner;
    bool finish = false;
    bool has_choose_all_children = false;
    mcts_node* after = nullptr;
    vector<Move> moves;
    vector<mcts_node*> children;
    vector<mcts_node*> unchoose_children;
    static void update(int _value, mcts_node* cur) {
        while (cur) {
            cur->visit += MIN_SIMULATE;
            if (cur->to_player == Blue) cur->value += _value;
            else cur->value += (MIN_SIMULATE - _value);
            cur = cur->parent;
        }
    }

    double ucb() const {
        return (double)value / (double)visit + MCTS_C * sqrt(log(parent->visit) / visit);
    }
};

class Hex {
public:
    int current_player = Red;
    int board[SIZE][SIZE] = { 0 };
    int dsuparent[SIZE * SIZE + 5] = { 0 };

    int dsu_find_father(int x) {

        return dsuparent[x] == 0 ? x : dsuparent[x] = dsu_find_father(dsuparent[x]);
    }

    void dsu_union(int x, int y) {
        int fx = dsu_find_father(x);
        int fy = dsu_find_father(y);
        if (fx != fy) {
            dsuparent[fx] = fy;
        }
    }

    void edge_cutoff(bool* out) {
        if (current_player == Red) {
            for (int i = 0; i < SIZE - 1; ++i) {
                if (board[0][i] == 0 && board[0][i + 1] == 0 && board[1][i] == 0) {
                    out[i] = true;
                    out[i + 1] = true;
                }
                if (board[SIZE - 1][i] == 0 && board[SIZE - 1][i + 1] == 0 && board[SIZE - 2][i + 1] == 0) {
                    out[(SIZE - 1) * SIZE + i] = true;
                    out[(SIZE - 1) * SIZE + i + 1] = true;
                }
            }
        }
        else {
            for (int i = 0; i < SIZE - 1; ++i) {
                if (board[i][0] == 0 && board[i + 1][0] == 0 && board[i][1] == 0) {
                    out[i * SIZE] = true;
                    out[(i + 1) * SIZE] = true;
                }
                if (board[i][SIZE - 1] == 0 && board[i + 1][SIZE - 1] == 0 && board[i + 1][SIZE - 2] == 0) {
                    out[i * SIZE + SIZE - 1] = true;
                    out[(i + 1) * SIZE + SIZE - 1] = true;
                }
            }
        }
    }

    static int get_value_simulate(int cur_board[SIZE][SIZE]) {

        stack<int> sk;
        bool vis[SIZE * SIZE] = { 0 };
        for (int i = 0; i < SIZE; ++i) {
            if (cur_board[0][i] == 1) sk.push(i);
            vis[i] = true;
        }
        while (!sk.empty()) {
            int index = sk.top();
            sk.pop();
            int x = index / SIZE, y = index % SIZE;
            for (int i = 0; i < 6; ++i) {
                int nx = x + BASIC_DIRECTION[i].x, ny = y + BASIC_DIRECTION[i].y;
                if (is_in_board(nx, ny) && cur_board[nx][ny] == 1) {
                    if (nx == SIZE - 1) return 1;
                    int pos = nx * SIZE + ny;
                    if (!vis[pos]) {
                        vis[pos] = true;
                        sk.push(pos);
                    }
                }
            }
        }
        return 0;
    }

    static bool is_in_board(int x, int y) {
        if (x >= 0 && x < SIZE && y >= 0 && y < SIZE) return true;
        return false;
    }

    void have_a_move(Move move) {
        board[move.x][move.y] = current_player;
        current_player = -current_player;
        int i = move.x, j = move.y;
        int pre_index = i * SIZE + j + 5;
        if (board[i][j] == Red) { // boundary_determination
            if (i == 0) dsu_union(pre_index, 1);
            if (i == 10) dsu_union(pre_index, 3);
        }
        else if (board[i][j] == Blue) {
            if (j == 0) dsu_union(pre_index, 4);
            if (j == 10) dsu_union(pre_index, 2);
        }
        for (int k = 0; k < 6; ++k) {
            int ni = i + BASIC_DIRECTION[k].x, nj = j + BASIC_DIRECTION[k].y;
            if (!is_in_board(ni, nj)) continue;
            if (board[i][j] == Red) {
                if (board[ni][nj] == Red) {
                    int new_index = ni * SIZE + nj + 5;
                    dsu_union(pre_index, new_index);
                }
            }
            else {
                if (board[ni][nj] == Blue) {
                    int new_index = ni * SIZE + nj + 5;
                    dsu_union(pre_index, new_index);
                }
            }
        }
    }

    int get_value() {
        if (dsu_find_father(1) == dsu_find_father(3)) return 1;
        else if (dsu_find_father(2) == dsu_find_father(4)) return -1;
        else return 0;
    }

    static bool have_4_same(int cur_board[SIZE][SIZE], int x, int y)
    {
        for (int i = 0; i < 6; ++i)
        {
            int f = 1;
            int c;
            int nx = x + BASIC_DIRECTION[i].x;
            int ny = y + BASIC_DIRECTION[i].y;
            if (nx < 0 || nx >= SIZE) c = 1;
            else if (ny < 0 || ny >= SIZE) c = -1;
            else c = cur_board[nx][ny];
            if (c == 0) continue;
            for (int j = 1; j < 4; j++ )
            {
                int nx = x + BASIC_DIRECTION[(i + j) % 6].x;
                int ny = y + BASIC_DIRECTION[(i + j) % 6].y;
                int color;
                if (nx < 0 || nx >= SIZE) color = 1;
                else if (ny < 0 || ny >= SIZE) color = -1;
                else color = cur_board[nx][ny];
                if (color != c)
                {
                    f = 0;
                    break;
                }
            }
            if (f == 1)
            {
                return true;
            }
        }
        return false;
    }

    static bool opposite_have_two_other_color(int cur_board[SIZE][SIZE], int x, int y)
    {
        for (int i = 0; i < 3; i++)
        {
            int nx0 = x + BASIC_DIRECTION[i].x;
            int ny0 = y + BASIC_DIRECTION[i].y;
            int color0;
            if (nx0 < 0 || nx0 >= SIZE) color0 = 1;
            else if (ny0 < 0 || ny0 >= SIZE) color0 = -1;
            else color0 = cur_board[nx0][ny0];

            if (color0 == 0)continue;

            int nx1 = x + BASIC_DIRECTION[i + 1].x;
            int ny1 = y + BASIC_DIRECTION[i + 1].y;
            int color1;
            if (nx1 < 0 || nx1 >= SIZE) color1 = 1;
            else if (ny1 < 0 || ny1 >= SIZE) color1 = -1;
            else color1 = cur_board[nx1][ny1];

            if (color0 != color1)continue;

            int opposite_nx0 = x + BASIC_DIRECTION[i + 3].x;
            int opposite_ny0 = y + BASIC_DIRECTION[i + 3].y;
            int opposite_color0;
            if (opposite_nx0 < 0 || opposite_nx0 >= SIZE) opposite_color0 = 1;
            else if (opposite_ny0 < 0 || opposite_ny0 >= SIZE) opposite_color0 = -1;
            else opposite_color0 = cur_board[opposite_nx0][opposite_ny0];

            if (color0 != -opposite_color0)continue;

            int opposite_nx1 = x + BASIC_DIRECTION[(i + 4) % 6].x;
            int opposite_ny1 = x + BASIC_DIRECTION[(i + 4) % 6].x;
            int opposite_color1;
            if (opposite_nx1 < 0 || opposite_nx1 >= SIZE) opposite_color1 = 1;
            else if (opposite_ny1 < 0 || opposite_ny1 >= SIZE) opposite_color1 = -1;
            else opposite_color1 = cur_board[opposite_nx1][opposite_ny1];

            if (color0 != -opposite_color1)continue;

            return true;
        }
        return false;
    }

    static bool have_1_opposite_3_diffcolor(int cur_board[SIZE][SIZE], int x, int y)
    {
        for (int i = 0; i < 6; ++i)
        {
            bool flag = true;
            int f = 1;
            int c;
            int nx = x + BASIC_DIRECTION[i].x;
            int ny = y + BASIC_DIRECTION[i].y;
            if (nx < 0 || nx >= SIZE) c = 1;
            else if (ny < 0 || ny >= SIZE) c = -1;
            else c = cur_board[nx][ny];
            if (c == 0) continue;
            for (int j = -1; j < 2; j+=2)
            {
                int nx = x + BASIC_DIRECTION[(i + j + 6) % 6].x;
                int ny = y + BASIC_DIRECTION[(i + j + 6) % 6].y;
                int color;
                if (nx < 0 || nx >= SIZE) color = 1;
                else if (ny < 0 || ny >= SIZE) color = -1;
                else color = cur_board[nx][ny];
                if (color != c)
                {
                    flag = false;
                    f = 0;
                    break;
                }
            }
            if (f == 1)
            {
                int nx = x + BASIC_DIRECTION[(i + 3) % 6].x;
                int ny = y + BASIC_DIRECTION[(i + 3) % 6].y;
                int color;
                if (nx < 0 || nx >= SIZE) color = 1;
                else if (ny < 0 || ny >= SIZE) color = -1;
                else color = cur_board[nx][ny];
                if (color != -c)
                {
                    flag = false;
                }
            }
            if (flag)
            {
                return true;
            }
        }
        return false;
    }


    vector<Move> available_moves() {
        vector<Move> ans;
        for (int x = 0; x < SIZE; ++x) {
            for (int y = 0; y < SIZE; ++y) {
                if (board[x][y] == 0 && !have_4_same(board, x, y) && !opposite_have_two_other_color(board, x, y)&&!have_1_opposite_3_diffcolor(board, x, y))
                {
                    ans.push_back({ x, y });
                }
            }
        }
        shuffle(ans.begin(), ans.end(), rng);
        return ans;
    }

    static bool attack_bridge_choice1(int cur_board[SIZE][SIZE], int x, int y, int& nx, int& ny) {
        int player = cur_board[x][y];
        vector<int> res;
        for (int i = 0; i < 6; ++i)
        {
            bool flag = true;
            for (int j = 0; j < 3; j += 2)
            {
                int nx = x + BASIC_DIRECTION[(i + j) % 6].x;
                int ny = y + BASIC_DIRECTION[(i + j) % 6].y;
                int color;
                if (nx < 0 || nx >= SIZE) color = 1;
                else if (ny < 0 || ny >= SIZE) color = -1;
                else color = cur_board[nx][ny];
                if (color != -player) //nx,ny涓嶆槸瀵规墜棰滆壊
                {
                    flag = false;
                }
            }
            if (flag)
            {
                int nx = x + BASIC_DIRECTION[(i + 1) % 6].x;
                int ny = y + BASIC_DIRECTION[(i + 1) % 6].y;
                if (is_in_board(nx, ny) && cur_board[nx][ny] == 0)
                {
                    res.push_back(nx * SIZE + ny);
                }
            }
        }
        if (res.size() == 0) return false;
        int num = res[rand() % res.size()];
        nx = num / SIZE;
        ny = num % SIZE;
        cur_board[num / SIZE][num % SIZE] = -player;
        return true;
    }

    int simulation(int x, int y) {
        int cur_board[SIZE][SIZE];
        int player = current_player;
        vector<Move> moves = available_moves();
        memcpy(cur_board, board, sizeof(board));
        int n = moves.size();//妫嬬洏涓婄殑绌烘牸鏁?
        int cnt = 0;
        while (cnt < n)
        {
            if (!attack_bridge_choice1(cur_board, x, y, x, y))
            {
                cur_board[moves[cnt].x][moves[cnt].y] = player;
                x = moves[cnt].x;
                y = moves[cnt].y;
            }
            player = -player;
            while (cnt < n && cur_board[moves[cnt].x][moves[cnt].y] != 0)
                cnt++;
        }
        return get_value_simulate(cur_board);
    }


    struct Edge {
        int next;
        int to;
    };
    struct Graph {
        int head[130];
        Edge edge[3000];
        int cnt;
        Graph() {
            memset(head, -1, sizeof(head));
            memset(edge, -1, sizeof(edge));
            cnt = 0;
        }

        Graph(const Graph& graph) {
            memcpy(head, graph.head, sizeof(graph.head));
            memcpy(edge, graph.edge, sizeof(graph.edge));
            cnt = graph.cnt;
        }
        void ini() {
            memset(head, -1, sizeof(head));
            memset(edge, -1, sizeof(edge));
            cnt = 0;
        }
    };

    Graph graph;

    void add(Graph& g, int from, int to) {
        bool flag = false;
        for (int inx = g.head[from]; inx != -1; inx = g.edge[inx].next) {
            int nto = g.edge[inx].to;
            if (nto == to) {
                flag = true;
                break;
            }
        }
        if (!flag) {
            g.edge[g.cnt].to = to;
            g.edge[g.cnt].next = g.head[from];
            g.head[from] = g.cnt++;
        }
    }

    void ini_red_graph() {
        graph.ini();

        bool vis[SIZE][SIZE] = { 0 };
        queue<int> q;

        for (int i = 0; i < SIZE; ++i) {
            for (int j = 0; j < SIZE; ++j) {
                if (board[i][j] != 0) continue;
                memset(vis, 0, sizeof(vis));
                int pos = i * SIZE + j;
                q.push(pos);
                vis[i][j] = true;
                if (i == 0) {
                    for (int k = 0; k < SIZE; ++k) {
                        if (k == j) continue;
                        if (board[0][k] == 0) {
                            add(graph, pos, k);
                            add(graph, k, pos);
                            vis[0][k] = true;
                        }
                        else if (board[0][k] == Red) {
                            q.push(k);
                            vis[0][k] = true;
                        }
                    }
                }
                else if (i == SIZE - 1) {
                    for (int k = 0; k < SIZE; ++k) {
                        if (k == j) continue;
                        if (board[SIZE - 1][k] == 0) {
                            add(graph, pos, (SIZE - 1) * SIZE + k);
                            add(graph, (SIZE - 1) * SIZE + k, pos);
                            vis[SIZE - 1][k] = true;
                        }
                        else if (board[SIZE - 1][k] == Red) {
                            q.push((SIZE - 1) * SIZE + k);
                            vis[SIZE - 1][k] = true;
                        }
                    }
                }
                while (!q.empty()) {
                    int npos = q.front();
                    q.pop();
                    int x = npos / SIZE, y = npos % SIZE;
                    for (int k = 0; k < 6; ++k) {

                        int nx = x + BASIC_DIRECTION[k].x, ny = y + BASIC_DIRECTION[k].y;

                        if (nx >= 0 && nx < SIZE && ny >= 0 && ny < SIZE && !vis[nx][ny]) {
                            if (board[nx][ny] == 0) {
                                add(graph, pos, nx * SIZE + ny);
                                add(graph, nx * SIZE + ny, pos);
                                vis[nx][ny] = true;
                            }
                            else if (board[nx][ny] == Red) {
                                q.push(nx * SIZE + ny);
                                vis[nx][ny] = true;
                            }
                        }

                    }
                }
            }
        }
    }

    void ini_blue_graph() {
        graph.ini();

        bool vis[SIZE][SIZE] = { 0 };
        queue<int> q;

        for (int i = 0; i < SIZE; ++i) {
            for (int j = 0; j < SIZE; ++j) {
                if (board[i][j] != 0) continue;
                memset(vis, 0, sizeof(vis));
                int pos = i * SIZE + j;
                q.push(pos);
                vis[i][j] = true;
                if (j == 0) {
                    for (int k = 0; k < SIZE; ++k) {
                        if (k == i) continue;
                        if (board[k][0] == 0) {
                            add(graph, pos, k * SIZE);
                            add(graph, k * SIZE, pos);
                            vis[k][0] = true;
                        }
                        else if (board[k][0] == Blue) {
                            q.push(k * SIZE);
                            vis[k][0] = true;
                        }
                    }
                }
                else if (j == SIZE - 1) {
                    for (int k = 0; k < SIZE; ++k) {
                        if (k == i) continue;
                        if (board[k][SIZE - 1] == 0) {
                            add(graph, pos, k * SIZE + SIZE - 1);
                            add(graph, k * SIZE + SIZE - 1, pos);
                            vis[k][SIZE - 1] = true;
                        }
                        else if (board[k][SIZE - 1] == Blue) {
                            //cout << "yes" << endl;
                            q.push(k * SIZE + SIZE - 1);
                            vis[k][SIZE - 1] = true;
                        }
                    }
                }
                while (!q.empty()) {
                    int npos = q.front();
                    q.pop();
                    int x = npos / SIZE, y = npos % SIZE;
                    for (int k = 0; k < 6; ++k) {

                        int nx = x + BASIC_DIRECTION[k].x, ny = y + BASIC_DIRECTION[k].y;

                        if (nx >= 0 && nx < SIZE && ny >= 0 && ny < SIZE && !vis[nx][ny]) {
                            if (board[nx][ny] == 0) {
                                add(graph, pos, nx * SIZE + ny);
                                add(graph, nx * SIZE + ny, pos);
                                vis[nx][ny] = true;
                            }
                            else if (board[nx][ny] == Blue) {
                                q.push(nx * SIZE + ny);
                                vis[nx][ny] = true;
                            }
                        }

                    }
                }
            }
        }
    }

    void ini_two_distance_red_up(Graph& red_up_graph) {
        queue<int> q;
        bool vis[SIZE][SIZE] = { 0 };
        for (int i = 0; i < SIZE; ++i) {
            if (board[0][i] == 0) {
                vis[0][i] = true;
                add(red_up_graph, i, SIZE * SIZE);
                add(red_up_graph, SIZE * SIZE, i);
            }
            else if (board[0][i] == Red) {
                q.push(i);
                vis[0][i] = true;
            }
        }
        while (!q.empty()) {
            int pos = q.front();
            q.pop();
            int x = pos / SIZE, y = pos % SIZE;
            for (int k = 0; k < 6; ++k) {
                int nx = x + BASIC_DIRECTION[k].x, ny = y + BASIC_DIRECTION[k].y;
                int npos = nx * SIZE + ny;
                if (nx >= 0 && nx < SIZE && ny >= 0 && ny < SIZE && !vis[nx][ny]) {
                    if (board[nx][ny] == 0) {
                        vis[nx][ny] = true;
                        add(red_up_graph, npos, SIZE * SIZE);
                        add(red_up_graph, SIZE * SIZE, npos);
                    }
                    else if (board[nx][ny] == Red) {
                        q.push(npos);
                        vis[nx][ny] = true;
                    }
                }
            }
        }
    }

    void ini_two_distance_red_down(Graph& red_down_graph) {
        queue<int> q;
        bool vis[SIZE][SIZE] = { 0 };
        for (int i = 0; i < SIZE; ++i) {
            int pos = (SIZE - 1) * SIZE + i;
            if (board[SIZE - 1][i] == 0) {
                vis[SIZE - 1][i] = true;
                add(red_down_graph, pos, SIZE * SIZE);
                add(red_down_graph, SIZE * SIZE, pos);
            }
            else if (board[SIZE - 1][i] == Red) {
                q.push(pos);
                vis[SIZE - 1][i] = true;
            }
        }
        while (!q.empty()) {
            int pos = q.front();
            q.pop();
            int x = pos / SIZE, y = pos % SIZE;
            for (int k = 0; k < 6; ++k) {
                int nx = x + BASIC_DIRECTION[k].x, ny = y + BASIC_DIRECTION[k].y;
                int npos = nx * SIZE + ny;
                if (nx >= 0 && nx < SIZE && ny >= 0 && ny < SIZE && !vis[nx][ny]) {
                    if (board[nx][ny] == 0) {
                        vis[nx][ny] = true;
                        add(red_down_graph, npos, SIZE * SIZE);
                        add(red_down_graph, SIZE * SIZE, npos);
                    }
                    else if (board[nx][ny] == Red) {
                        q.push(npos);
                        vis[nx][ny] = true;
                    }
                }
            }
        }
    }

    void ini_two_distance_blue_up(Graph& blue_up_graph) {
        queue<int> q;
        bool vis[SIZE][SIZE] = { 0 };
        for (int i = 0; i < SIZE; ++i) {
            int pos = i * SIZE;
            if (board[i][0] == 0) {
                vis[i][0] = true;
                add(blue_up_graph, pos, SIZE * SIZE);
                add(blue_up_graph, SIZE * SIZE, pos);
            }
            else if (board[i][0] == Blue) {
                q.push(pos);
                vis[i][0] = true;
            }
        }
        while (!q.empty()) {
            int pos = q.front();
            q.pop();
            int x = pos / SIZE, y = pos % SIZE;
            for (int k = 0; k < 6; ++k) {
                int nx = x + BASIC_DIRECTION[k].x, ny = y + BASIC_DIRECTION[k].y;
                int npos = nx * SIZE + ny;
                if (nx >= 0 && nx < SIZE && ny >= 0 && ny < SIZE && !vis[nx][ny]) {
                    if (board[nx][ny] == 0) {
                        vis[nx][ny] = true;
                        add(blue_up_graph, npos, SIZE * SIZE);
                        add(blue_up_graph, SIZE * SIZE, npos);
                    }
                    else if (board[nx][ny] == Blue) {
                        q.push(npos);
                        vis[nx][ny] = true;
                    }
                }
            }
        }
    }

    void ini_two_distance_blue_down(Graph& blue_down_graph) {
        queue<int> q;
        bool vis[SIZE][SIZE] = { 0 };
        for (int i = 0; i < SIZE; ++i) {
            int pos = i * SIZE + SIZE - 1;
            if (board[i][SIZE - 1] == 0) {
                vis[i][SIZE - 1] = true;
                add(blue_down_graph, pos, SIZE * SIZE);
                add(blue_down_graph, SIZE * SIZE, pos);
            }
            else if (board[i][SIZE - 1] == Blue) {
                q.push(pos);
                vis[i][SIZE - 1] = true;
            }
        }
        while (!q.empty()) {
            int pos = q.front();
            q.pop();
            int x = pos / SIZE, y = pos % SIZE;
            for (int k = 0; k < 6; ++k) {
                int nx = x + BASIC_DIRECTION[k].x, ny = y + BASIC_DIRECTION[k].y;
                int npos = nx * SIZE + ny;
                if (nx >= 0 && nx < SIZE && ny >= 0 && ny < SIZE && !vis[nx][ny]) {
                    if (board[nx][ny] == 0) {
                        vis[nx][ny] = true;
                        add(blue_down_graph, npos, SIZE * SIZE);
                        add(blue_down_graph, SIZE * SIZE, npos);
                    }
                    else if (board[nx][ny] == Blue) {
                        q.push(npos);
                        vis[nx][ny] = true;
                    }
                }
            }
        }
    }

    void two_disttance_cal(const Graph & the_graph, int* out) {
        int third_dist[130];
        memset(third_dist, INF, sizeof(third_dist));
        third_dist[SIZE * SIZE] = 0;
        for (int inx = the_graph.head[SIZE * SIZE]; inx != -1; inx = the_graph.edge[inx].next) {
            int pos = the_graph.edge[inx].to;
            third_dist[pos] = 1;
        }

        bool flag = false;

        while (true) {

            flag = false;

            for (int i = 0; i < SIZE; ++i) {
                for (int j = 0; j < SIZE; ++j) {
                    int pos = i * SIZE + j;
                    int mi = INF, submi = INF;
                    for (int inx = the_graph.head[pos]; inx != -1; inx = the_graph.edge[inx].next) {
                        int npos = the_graph.edge[inx].to;
                        int nx = npos / SIZE, ny = npos % SIZE;
                        if (third_dist[npos] < mi) {
                            submi = mi;
                            mi = third_dist[npos];
                            //cout << mi << endl;
                        } else if (third_dist[npos] < submi) {
                            submi = third_dist[npos];
                        }
                    }

                    if (submi + 1 < third_dist[pos]) {
                        third_dist[pos] = submi + 1;
                        flag = true;
                    }
                }
            }
            if (!flag) break;
        }

        for (int i = 0; i < SIZE * SIZE; ++i) {
            out[i] = third_dist[i];
        }
    }

    bool two_distacne_cutoff(bool* out, mcts_node* u) {
        Graph up_graph;
        Graph down_graph;
        int two_distance_up[130];
        int two_distance_down[130];
        int two_distance_sum[130];
        memset(two_distance_sum, INF, sizeof(two_distance_sum));
        if (current_player == Red) {
            ini_red_graph();
            up_graph = graph;
            down_graph = graph;
            ini_two_distance_red_up(up_graph);
            ini_two_distance_red_down(down_graph);
        }
        else {
            ini_blue_graph();
            up_graph = graph;
            down_graph = graph;
            ini_two_distance_blue_up(up_graph);
            ini_two_distance_blue_down(down_graph);
        }

        two_disttance_cal(up_graph, two_distance_up);
        two_disttance_cal(down_graph, two_distance_down);

        bool flag = false;

        for (int i = 0; i < SIZE * SIZE; ++i) {
            two_distance_sum[i] = two_distance_up[i] + two_distance_down[i];
            if (two_distance_sum[i] < INF) flag = true;
        }

        if (!flag) {
            if (u->parent) return false;
            board_cutoff(out);
            return true;
        }

        sort(two_distance_sum, two_distance_sum + SIZE * SIZE);

        int gate = two_distance_sum[0];
        int it = 0;
        for (int i = 0; i < LAYER; i++) {
            while (it < SIZE * SIZE && two_distance_sum[it] == gate) {
                it++;
            }
            gate = two_distance_sum[it];
            if (gate >= INF) {
                gate = INF;
                break;
            }
        }
        for (int i = 0; i < SIZE * SIZE; ++i) {
            if (two_distance_up[i] + two_distance_down[i] >= gate) out[i] = true;
        }

        return true;
    }
    void board_cutoff(bool* out) {
        for (int i = 0; i < SIZE; ++i) {
            for (int j = 0; j < SIZE; ++j) {
                if (board[i][j] != 0) out[i * SIZE + j] = true;
            }
        }
    }

};

class Mcts {
public:
    Hex game;
    chrono::steady_clock::time_point start;
    bool timeout() {
        return chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - start).count() > TIMELIMIT;
    }
    static mcts_node* find_best_children(mcts_node* u) {
        if (!u->has_choose_all_children) {
            mcts_node* v = u->unchoose_children.back();
            u->unchoose_children.pop_back();
            if (u->unchoose_children.size() == 0) u->has_choose_all_children = true;
            return v;
        }
        mcts_node* choice = nullptr;
        double ma = -1;

        for (auto v : u->children) {
            const double ucb = v->ucb();
            if (ucb > ma) {
                ma = ucb;
                choice = v;
            }
        }
        return choice;
    }

    mcts_node* find_best_answer(mcts_node* u) {
        mcts_node* choice = nullptr;
        int ma = -1;

        for (auto v : u->children) {
            if (v->isend && v->winner == u->to_player) return v;
            if (v->visit > ma) {
                ma = v->visit;
                choice = v;
            }
        }
        return choice;
    }

    bool expand(mcts_node* u) {
        bool cut[SIZE * SIZE] = { 0 };
        if (!game.two_distacne_cutoff(cut, u))return false;
        game.edge_cutoff(cut);
        vector<int> expand_child;
        for (int i = 0; i < SIZE * SIZE; ++i) {
            if (cut[i]) continue;
            expand_child.push_back(i);
        }
        for (int child : expand_child) {
            mcts_node* v = new mcts_node{ {child / SIZE, child % SIZE}, u, -(u->to_player) };
            u->children.push_back(v);
            u->unchoose_children.push_back(v);
        }
        shuffle((u->children.begin()), (u->children.end()), rng);
        return true;
    }



    void search(mcts_node* u) {
        while (u->finish) {
            u = find_best_children(u);
            game.have_a_move(u->node_move);
        }


        if (u->isend) {
            if (u->winner == Red) u->update(MIN_SIMULATE, u);
            else u->update(0, u);
            return;
        }

        if (u->visit == 0) {
            int winner = game.get_value();
            if (winner) {
                u->isend = true;
                u->winner = winner;
                if (u->winner == Red) u->update(MIN_SIMULATE, u);
                else u->update(0, u);
                return;
            }
        }

        if (u->visit < MAX_SIMULATE) {

            int res = 0;
            for (int i = 0; i < TIMES_SIMULATE; ++i) {
                res += game.simulation(u->node_move.x, u->node_move.y);
            }
            u->update(res, u);
        }

        if (u->visit == MAX_SIMULATE) {
            if (expand(u)) {
                u->finish = true;
            }
            else {
                u->isend = true;
                u->winner = -(u->to_player);
            }
        }
    }

    int play(const Hex& currentGame) {
        start = chrono::steady_clock::now();
        mcts_node* root = new mcts_node();
        root->to_player = currentGame.current_player;
        while (!timeout()) {
            game = currentGame;
            search(root);
        }
        mcts_node* choice = find_best_answer(root);
        return choice->node_move.x * 11 + choice->node_move.y;
    }
};

class IO {
public:
    int R[100][2];
    int B[100][2];
    int Rsize = 0;
    int Bsize = 0;
    void reload() {
        ifstream infile;
        string file_name = "chess.txt";
        file_name = "D:\\Clion\\mcts\\" + file_name;
        infile.open(file_name);
        string str;
        getline(infile, str);
        infile.close();
        int cur = 0;
        int len = str.size();
        while (cur < len) {
            if (str[cur] == ';') {
                char color = str[++cur];
                if (!(color =='R' || color == 'B')) continue;
                cur++;
                char y = str[++cur];
                cur++;
                cur++;
                int x = 0;
                while(str[cur] >= '0' && str[cur] <= '9') {
                    x = x * 10 + str[cur] - '0';
                    cur++;
                }
                if (color == 'R') {
                    R[Rsize][0] = 11 - x;
                    R[Rsize][1] = y - 'A';
                    Rsize++;
                } else {
                    B[Bsize][0] = 11 - x;
                    B[Bsize][1] = y - 'A';
                    Bsize++;
                }
            }
            cur++;
        }
    }

    void print_message(ofstream & outfile){}

    void print() {
        ofstream outfile;
        ofstream logfile;
        string file_name = "chess.txt";
        file_name = "D:\\Clion\\mcts\\" + file_name;
        outfile.open(file_name);
        logfile.open("D:\\Clion\\mcts\\log.txt", ios::app);

        logfile << '\n';
        logfile << '\n';

        outfile << '{';
        outfile << "[绾夸笂]";
        logfile << '{';
        logfile << "[绾夸笂]";
        print_message(outfile);
        bool flag = false;
        int rsize = 0;
        int bsize = 0;
        //cout << ":" << Rsize << ' ' << Bsize << endl;
        while (true) {
            if (!flag) {
                if (rsize == Rsize) break;
                outfile << ";R(";
                outfile << (char)('A' + R[rsize][1]);
                outfile << ',';
                outfile << 11 - R[rsize][0];
                outfile << ")";
                logfile << ";R(";
                logfile << (char)('A' + R[rsize][1]);
                logfile << ',';
                logfile << 11 - R[rsize][0];
                logfile << ")";
                rsize++;
            } else {
                if (bsize == Bsize) break;
                outfile << ";B(";
                outfile << (char)('A' + B[bsize][1]);
                outfile << ',';
                outfile << 11 - B[bsize][0];
                outfile << ")";
                logfile << ";B(";
                logfile << (char)('A' + B[bsize][1]);
                logfile << ',';
                logfile << 11 - B[bsize][0];
                logfile << ")";
                bsize++;
            }
            if (flag) flag = false;
            else flag = true;
        }
        outfile << '}';
        logfile << '}';
    }
};

class Judge {
public:
    static int is_start(int x, int y, IO& io) {
        if (x < 0 || x >= 11 || y < 0 || y >= 11) return 1;
        for (int i = 0; i < io.Rsize; ++i) {
            if (io.R[i][0] == x && io.R[i][1] == y) return 2;
        }
        for (int i = 0; i < io.Bsize; ++i) {
            if (io.B[i][0] == x && io.B[i][1] == y) return 2;
        }
        return 0;
    }

    static int is_win(IO& io) {
        int board[11][11];
        for (int i = 0; i < io.Rsize; ++i) {
            board[io.R[i][0]][io.R[i][1]] = Red;
        }
        for (int i = 0; i < io.Bsize; ++i) {
            board[io.B[i][0]][io.B[i][1]] = Blue;
        }
        queue<int> q;
        bool vis[121];
        for (int i = 0; i < 121; ++i) vis[i] = false;
        for (int i = 0; i < 11; ++i) {
            if (board[0][i] == Red) {
                q.push(i);
            }
        }
        while (!q.empty()) {
            int x = q.front() / 11, y = q.front() % 11;
            q.pop();
            if (x == 10) return Red;
            for (int i = 0; i < 6; ++i) {
                int nx = x + BASIC_DIRECTION[i].x, ny = y + BASIC_DIRECTION[i].y;
                int pos = nx * 11 + ny;
                if (nx >=0 && nx < 11 && ny >= 0 && ny < 11 && board[nx][ny] == Red && !vis[pos]) {
                    q.push(pos);
                    vis[pos] = true;
                }
            }
        }
        for (int i = 0; i < 121; ++i) vis[i] = false;
        for (int i = 0; i < 11; ++i) {
            if (board[i][0] == Blue) {
                q.push(i * 11);
            }
        }
        while (!q.empty()) {
            int x = q.front() / 11, y = q.front() % 11;
            q.pop();
            if (y == 10) return Blue;
            for (int i = 0; i < 6; ++i) {
                int nx = x + BASIC_DIRECTION[i].x, ny = y + BASIC_DIRECTION[i].y;
                int pos = nx * 11 + ny;
                if (nx >=0 && nx < 11 && ny >= 0 && ny < 11 && board[nx][ny] == Blue && !vis[pos]) {
                    q.push(pos);
                    vis[pos] = true;
                }
            }
        }
        return 0;
    }
};

int main()
{
    ios::sync_with_stdio(false),cin.tie(NULL);

    char x;
    int y;
    cin >> x >> y;
    Judge* judge = nullptr;
    if (USE_JUDGE) {
        judge = new Judge();
    }
    Hex new_game;
    IO io;
    io.reload();

    if (y == -1) {
        io.R[io.Rsize][0] = 3;
        io.R[io.Rsize][1] = 7;
        io.Rsize++;
        io.print();
        cout << "R(H,8)";
        return 0;
    }

    if (USE_JUDGE) {
        int result = judge->is_start(11 - y, x - 'A', io);
        if (result == 1) {
            if (io.Rsize = io.Bsize) {
                io.R[io.Rsize][0] = 11 - y;
                io.R[io.Rsize][1] = x - 'A';
                io.Rsize++;
                cout << "B鑳滃埄";
            } else {
                io.B[io.Bsize][0] = 11 - y;
                io.B[io.Bsize][1] = x - 'A';
                io.Bsize++;
                cout << "R鑳滃埄";
            }
            io.print();
            cout << " (瀵规墜涓嬫浣嶇疆涓嶅湪鍚堟硶鑼冨洿)";
            return 0;
        }
        if (result == 2) {
            if (io.Rsize == io.Bsize) {
                io.R[io.Rsize][0] = 11 - y;
                io.R[io.Rsize][1] = x - 'A';
                io.Rsize++;
                cout << " B鑳滃埄";
            } else {
                io.B[io.Bsize][0] = 11 - y;
                io.B[io.Bsize][1] = x - 'A';
                io.Bsize++;
                cout << " R鑳滃埄";
            }
            io.print();
            cout << " (瀵规墜涓嬫浣嶇疆宸叉湁妫嬪瓙)";
            return 0;
        }
    }


    if (io.Rsize == io.Bsize) {
        io.R[io.Rsize][0] = 11 - y;
        io.R[io.Rsize][1] = x - 'A';
        io.Rsize++;
    } else {
        io.B[io.Bsize][0] = 11 - y;
        io.B[io.Bsize][1] = x - 'A';
        io.Bsize++;
    }

    if (USE_JUDGE) {
        int result = judge->is_win(io);
        if (result != 0) {
            if (result == Red) cout << " R鑳滃埄";
            else cout << " B鑳滃埄";
            cout << " (瀵规墜宸茬粡鑳滃埄)";
            io.print();
            return 0;
        }
    }

    int turnID = io.Bsize;
    for (int i = 0; i < turnID; i++) {
        new_game.have_a_move({ io.R[i][0], io.R[i][1] });
        new_game.have_a_move({ io.B[i][0], io.B[i][1]});
    }

    if (io.Rsize != io.Bsize) {
        new_game.have_a_move({ io.R[turnID][0], io.R[turnID][1] });
    }
    Mcts mcts;
    int ans = mcts.play(new_game);
    int nx = ans / 11, ny = ans % 11;
    if (io.Rsize == io.Bsize) {
        cout << "R(" << (char)('A' + ny) << ',' << 11 - nx << ')';
        io.R[io.Rsize][0] = nx;
        io.R[io.Rsize][1] = ny;
        io.Rsize++;
        io.print();
        if (USE_JUDGE) {
            int result = judge->is_win(io);
            if (result != 0) {
                if (result == Red) cout << " R鑳滃埄";
                else cout << " B鑳滃埄";
                cout << " (鑷繁鑳滃埄)";
                return 0;
            }
        }
    } else {
        cout << "B(" << (char)('A' + ny) << ',' << 11 - nx << ')';
        io.B[io.Bsize][0] = nx;
        io.B[io.Bsize][1] = ny;
        io.Bsize++;
        io.print();
        if (USE_JUDGE) {
            int result = judge->is_win(io);
            if (result != 0) {
                if (result == Red) cout << " R鑳滃埄";
                else cout << " B鑳滃埄";
                cout << " (鑷繁鑳滃埄)";
                return 0;
            }
        }
    }
}