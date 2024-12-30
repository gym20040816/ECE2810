#include <vector>
#include <string>
#include <iostream>
#include <queue>
#include <set>
#include <map>
#include <unordered_set>
#include <algorithm>
#include <climits>
#include <cstdint>

using std::vector;
using std::string;
using std::pair;
using std::queue;
using std::set;
using std::map;
using std::unordered_set;
using std::make_pair;
using std::abs;
using std::find;
using std::sort;
using std::min;
using std::fill;
using std::cout;
using std::endl;
using std::cin;
using std::ios_base;
using std::priority_queue;
using std::hash;

const int directions[4][2] = {
    {-1, 0}, 
    {1, 0},
    {0, -1},
    {0, 1}
};

// 添加类型选择函数
template<typename T>
struct CoordTraits {
    using type = T;
    static constexpr bool is_valid = false;
};

template<>
struct CoordTraits<uint8_t> {
    using type = uint8_t;
    static constexpr bool is_valid = true;
    static constexpr size_t max_size = 256;
};

template<>
struct CoordTraits<uint16_t> {
    using type = uint16_t;
    static constexpr bool is_valid = true;
    static constexpr size_t max_size = 65536;
};

template<>
struct CoordTraits<uint32_t> {
    using type = uint32_t;
    static constexpr bool is_valid = true;
    static constexpr size_t max_size = 4294967296;
};

// 根据网格大小选择合适的类型
template<typename T = size_t>
T selectCoordType(size_t rows, size_t cols) {
    size_t total_size = rows * cols;
    if (total_size <= CoordTraits<uint8_t>::max_size) {
        return static_cast<T>(sizeof(uint8_t));
    } else if (total_size <= CoordTraits<uint16_t>::max_size) {
        return static_cast<T>(sizeof(uint16_t));
    } else {
        return static_cast<T>(sizeof(uint32_t));
    }
}

// 修改原有的 toIndex 和 toCoords 为模板函数
template<typename T>
inline T toIndex(T r, T c, T m) {
    return static_cast<T>(static_cast<size_t>(r) * static_cast<size_t>(m) + static_cast<size_t>(c));
}

template<typename T>
inline pair<T, T> toCoords(T index, T m) {
    return {index / m, index % m};
}

// 修改 State 结构为模板类
template<typename T>
struct State {
    T player;
    vector<T> boxes;
    int f_score;
    int g_score;

    bool operator==(const State& other) const {
        return player == other.player && boxes == other.boxes;
    }

    bool operator<(const State& other) const {
        return f_score > other.f_score;
    }

    struct Hash {
        size_t operator()(const State& state) const {
            // 使用 FNV-1a 哈希算法
            static const size_t FNV_PRIME = 1099511628211ULL;
            static const size_t FNV_OFFSET = 14695981039346656037ULL;
            
            size_t hash = FNV_OFFSET;
            
            // 哈希玩家位置
            hash ^= state.player;
            hash *= FNV_PRIME;
            
            // 哈希箱子位置
            for (T box : state.boxes) {
                hash ^= box;
                hash *= FNV_PRIME;
            }
            
            return hash;
        }
    };
};

// 修改方向数组的定义，使用模板
template<typename T>
T safeAdd(T a, int b) {
    if (b < 0) {
        return static_cast<T>(static_cast<int64_t>(a) - static_cast<int64_t>(-b));
    } else {
        return static_cast<T>(static_cast<int64_t>(a) + static_cast<int64_t>(b));
    }
}

// 修改 Solution 类为模板类
template<typename T>
class Solution {
private:
    // 更新成员变量类型
    vector<pair<T, T>> cached_targets;
    T last_grid_rows = 0;
    T last_grid_cols = 0;
    
    // 添加路径缓存成员变量
    struct PairCompare {
        template <class T1, class T2>
        bool operator()(const pair<T1, T2>& a, const pair<T1, T2>& b) const {
            if (a.first != b.first) return a.first < b.first;
            return a.second < b.second;
        }
    };
    
    mutable map<
        pair<pair<T, T>, pair<T, T>>, 
        bool, 
        PairCompare
    > path_cache;

    mutable map<T, int> box_to_target_distance_cache; // 添加缓存

    // 缓存曼哈顿距离
    mutable map<pair<T, T>, int> manhattan_cache;
    
    // 计算两点间的曼哈顿距离
    int getManhattanDistance(T x1, T y1, T x2, T y2) const {
        // 使用固定的列数（从目标点缓存获取）
        T cols = last_grid_cols;  // 使用类成员变量
        auto key = make_pair(toIndex(x1, y1, cols),
                            toIndex(x2, y2, cols));
        auto it = manhattan_cache.find(key);
        if (it != manhattan_cache.end()) {
            return it->second;
        }
        int dist = abs(static_cast<int>(x1) - static_cast<int>(x2)) + 
                   abs(static_cast<int>(y1) - static_cast<int>(y2));
        manhattan_cache[key] = dist;
        return dist;
    }

    // 计算箱子到最近目标点的距离
    int getBoxToTargetDistance(T box_r, T box_c, 
                             [[maybe_unused]] const vector<vector<char>>& grid) const {
        int min_dist = INT_MAX;
        for (const auto& target : cached_targets) {
            int dist = getManhattanDistance(box_r, box_c, 
                                          target.first, target.second);
            min_dist = min(min_dist, dist);
        }
        return min_dist;
    }

    // 添加匈牙利算法相关的成员变量
    vector<vector<int>> cost_matrix;  // 存储箱子到目标点的距离矩阵
    vector<int> lx, ly;              // 顶标值
    vector<int> match_y;             // 记录每个目标点匹配的箱子
    vector<bool> visit_y;            // 记录每个目标点是否被访问
    const int INF = INT_MAX / 2;     // 避免溢出的无穷大值
    
    // 匈牙利算法的核心函数
    bool find(int x, int min_delta) {
        for (size_t y = 0; y < cost_matrix[0].size(); ++y) {
            if (!visit_y[y]) {
                int t = lx[x] + ly[y] - cost_matrix[x][y];
                if (t == 0) {
                    visit_y[y] = true;
                    if (match_y[y] == -1 || find(match_y[y], min_delta)) {
                        match_y[y] = x;
                        return true;
                    }
                } else {
                    min_delta = min(min_delta, t);
                }
            }
        }
        return false;
    }
    
    // KM算法实现最优匹配
    int KM() {
        size_t n = cost_matrix.size();    // 箱子数量
        size_t m = cost_matrix[0].size(); // 目标点数量
        
        // 初始化顶标
        lx.assign(n, -INF);
        ly.assign(m, 0);
        for (size_t i = 0; i < n; ++i) {
            for (size_t j = 0; j < m; ++j) {
                lx[i] = std::max(lx[i], cost_matrix[i][j]);
            }
        }
        
        // 初始化匹配
        match_y.assign(m, -1);
        
        // 对每个箱子寻找匹配
        for (size_t x = 0; x < n; ++x) {
            while (true) {
                visit_y.assign(m, false);
                int min_delta = INF;
                if (find(x, min_delta)) break;
                
                // 更新顶标
                for (size_t i = 0; i < n; ++i) {
                    if (visit_y[i]) ly[i] += min_delta;
                }
                lx[x] -= min_delta;
            }
        }
        
        // 计算最优匹配的总代价
        int total_cost = 0;
        for (size_t y = 0; y < m; ++y) {
            if (match_y[y] != -1) {
                total_cost += cost_matrix[match_y[y]][y];
            }
        }
        return total_cost;
    }
    
    // 构建代价矩阵
    void buildCostMatrix(const State<T>& state, const vector<vector<char>>& grid) {
        T m = grid[0].size();
        size_t n_boxes = state.boxes.size();
        
        // 确保目标点已经被缓存
        if (cached_targets.empty()) {
            for (T r = 0; r < grid.size(); ++r) {
                for (T c = 0; c < grid[0].size(); ++c) {
                    if (grid[r][c] == 'T' || grid[r][c] == 'R') {
                        cached_targets.push_back({r, c});
                    }
                }
            }
        }
        
        // 构建代价矩阵
        cost_matrix.assign(n_boxes, vector<int>(cached_targets.size(), 0));
        for (size_t i = 0; i < n_boxes; ++i) {
            auto [box_r, box_c] = toCoords(state.boxes[i], m);
            for (size_t j = 0; j < cached_targets.size(); ++j) {
                const auto& target = cached_targets[j];
                // 计算曼哈顿距离作为基础代价
                int base_cost = getManhattanDistance(box_r, box_c, target.first, target.second);
                
                // 添加额外的代价因素
                int extra_cost = 0;
                
                // 1. 如果箱子已经在目标点上，给予奖励
                if (grid[box_r][box_c] == 'T' || grid[box_r][box_c] == 'R') {
                    extra_cost -= 50;
                }
                
                // 2. 如果箱子在角落或边缘，增加代价
                bool near_wall = false;
                if ((box_r == 0 || grid[box_r-1][box_c] == '#') ||
                    (box_r == grid.size()-1 || grid[box_r+1][box_c] == '#') ||
                    (box_c == 0 || grid[box_r][box_c-1] == '#') ||
                    (box_c == grid[0].size()-1 || grid[box_r][box_c+1] == '#')) {
                    near_wall = true;
                    extra_cost += 20;
                }
                
                // 3. 如果目标点在角落，对非角落的箱子增加代价
                bool target_in_corner = 
                    ((target.first == 0 || grid[target.first-1][target.second] == '#') &&
                     (target.second == 0 || grid[target.first][target.second-1] == '#')) ||
                    ((target.first == 0 || grid[target.first-1][target.second] == '#') &&
                     (target.second == grid[0].size()-1 || grid[target.first][target.second+1] == '#')) ||
                    ((target.first == grid.size()-1 || grid[target.first+1][target.second] == '#') &&
                     (target.second == 0 || grid[target.first][target.second-1] == '#')) ||
                    ((target.first == grid.size()-1 || grid[target.first+1][target.second] == '#') &&
                     (target.second == grid[0].size()-1 || grid[target.first][target.second+1] == '#'));
                
                if (target_in_corner && !near_wall) {
                    extra_cost += 30;
                }
                
                cost_matrix[i][j] = base_cost + extra_cost;
            }
        }
    }
    
    // 修改现有的启发式函数，使用匈牙利算法
    int calculateStateWeight(const State<T>& state, const vector<vector<char>>& grid) const {
        int weight = 0;
        T m = grid[0].size();
        
        // 构建并求解匹配问题
        buildCostMatrix(state, grid);
        weight = KM();
        
        // 添加玩家到最近未完成箱子的距离
        auto [player_r, player_c] = toCoords(state.player, m);
        int min_player_dist = INT_MAX;
        for (T box : state.boxes) {
            auto [box_r, box_c] = toCoords(box, m);
            if (grid[box_r][box_c] != 'T' && grid[box_r][box_c] != 'R') {
                int dist = getManhattanDistance(player_r, player_c, box_r, box_c);
                min_player_dist = min(min_player_dist, dist);
            }
        }
        if (min_player_dist != INT_MAX) {
            weight += min_player_dist * 5;
        }
        
        return weight + state.g_score * 8;
    }

    // 添加初始化缓存的函数
    void initializeCache(const vector<vector<char>>& grid) {
        if (last_grid_rows != static_cast<T>(grid.size()) || 
            last_grid_cols != static_cast<T>(grid[0].size())) {
            last_grid_rows = static_cast<T>(grid.size());
            last_grid_cols = static_cast<T>(grid[0].size());
            
            // 缓存死角网格
            // cached_deadlock_grid = grid;
            // for (size_t r = 0; r < grid.size(); ++r) {
            //     for (size_t c = 0; c < grid[0].size(); ++c) {
            //         if (grid[r][c] != '#' && grid[r][c] != 'T' && grid[r][c] != 'R') {
            //             bool top_wall = (r == 0) || (grid[r-1][c] == '#');
            //             bool bottom_wall = (r == grid.size()-1) || (grid[r+1][c] == '#');
            //             bool left_wall = (c == 0) || (grid[r][c-1] == '#');
            //             bool right_wall = (c == grid[0].size()-1) || (grid[r][c+1] == '#');
                        
            //             if ((top_wall && left_wall) || (top_wall && right_wall) || 
            //                 (bottom_wall && left_wall) || (bottom_wall && right_wall)) {
            //                 cached_deadlock_grid[r][c] = 'X';
            //             }
            //         }
            //     }
            // }
            
            // 缓存目标点位置
            cached_targets.clear();
            for (size_t r = 0; r < grid.size(); ++r) {
                for (size_t c = 0; c < grid[0].size(); ++c) {
                    if (grid[r][c] == 'T' || grid[r][c] == 'R') {
                        cached_targets.push_back({r, c});
                    }
                }
            }
        }
    }

    // 修改现有的 floodFill 函数为带缓存版本
    bool floodFill(pair<T, T> start, 
                   const vector<vector<char>>& current_grid, 
                   pair<T, T> target) const {
        // 快速路径：如果起点和终点相同
        if (start == target) return true;
        
        // 检查缓存
        auto key = make_pair(start, target);
        auto it = path_cache.find(key);
        if (it != path_cache.end()) {
            return it->second;
        }
        
        // 使用静态数组避免重复分配内存
        static vector<vector<bool>> visited;
        visited.resize(current_grid.size(), vector<bool>(current_grid[0].size(), false));
        for(auto& row : visited) {
            fill(row.begin(), row.end(), false);
        }
        
        // 使用栈进行 DFS
        static vector<pair<T, T>> stack;
        stack.clear();
        stack.push_back(start);
        visited[start.first][start.second] = true;
        
        bool result = false;
        while (!stack.empty()) {
            auto [r, c] = stack.back();
            stack.pop_back();
            
            for (const auto& dir : directions) {
                int64_t new_r = static_cast<int64_t>(r) + dir[0];
                int64_t new_c = static_cast<int64_t>(c) + dir[1];
                
                if (new_r >= 0 && new_c >= 0 && 
                    new_r < static_cast<int64_t>(current_grid.size()) && 
                    new_c < static_cast<int64_t>(current_grid[0].size())) {
                    
                    T ur = static_cast<T>(new_r);
                    T uc = static_cast<T>(new_c);
                    
                    if (!visited[ur][uc] && current_grid[ur][uc] != '#' && current_grid[ur][uc] != 'X' && current_grid[ur][uc] != 'Y') {
                        if (ur == target.first && uc == target.second) {
                            result = true;
                            break;
                        }
                        visited[ur][uc] = true;
                        stack.push_back({ur, uc});
                    }
                }
            }
            if (result) break;
        }
        
        // 存储结果到缓存
        path_cache[key] = result;
        return result;
    }

    // 在每次新的搜索开始时清除缓存
    void clearCache() {
        path_cache.clear();
    }

    // 添加一个专门用于检查玩家到箱子可达性的轻量级函数
    bool canPlayerReachBox(T player_r, T player_c, 
                          T box_r, T box_c,
                          const vector<vector<char>>& grid) const {
        if (player_r == box_r && player_c == box_c) return true;
        
        const T rows = static_cast<T>(grid.size());
        const T cols = static_cast<T>(grid[0].size());
        
        static vector<vector<bool>> forward_visited;
        static vector<vector<bool>> backward_visited;
        forward_visited.resize(rows, vector<bool>(cols));
        backward_visited.resize(rows, vector<bool>(cols));
        
        for(auto& row : forward_visited) fill(row.begin(), row.end(), false);
        for(auto& row : backward_visited) fill(row.begin(), row.end(), false);
        
        static queue<pair<T, T>> forward_q, backward_q;
        while(!forward_q.empty()) forward_q.pop();
        while(!backward_q.empty()) backward_q.pop();
        
        forward_visited[player_r][player_c] = true;
        backward_visited[box_r][box_c] = true;
        forward_q.push({player_r, player_c});
        backward_q.push({box_r, box_c});
        
        // 跳跃搜索的核心函数
        auto jumpPoint = [&](T r, T c, int dir_r, int dir_c, const vector<vector<bool>>& other_visited) -> pair<T, T> {
            T curr_r = r;
            T curr_c = c;
            
            while (true) {
                // 计算下一个位置
                T next_r = curr_r + static_cast<T>(dir_r);
                T next_c = curr_c + static_cast<T>(dir_c);
                
                // 检查边界和墙
                if (next_r >= rows || next_c >= cols || grid[next_r][next_c] == '#') {
                    return {curr_r, curr_c};
                }
                
                // 如果找到对方的访问点，返回当前位置
                if (other_visited[next_r][next_c]) {
                    return {next_r, next_c};
                }
                
                // 检查是否有转角点
                bool has_turn = false;
                for (const auto& check_dir : directions) {
                    if (check_dir[0] == dir_r && check_dir[1] == dir_c) continue;
                    
                    T check_r = next_r + static_cast<T>(check_dir[0]);
                    T check_c = next_c + static_cast<T>(check_dir[1]);
                    
                    if (check_r < rows && check_c < cols && 
                        grid[check_r][check_c] != '#') {
                        has_turn = true;
                        break;
                    }
                }
                
                // 如果是转角点，返回下一个位置
                if (has_turn) {
                    return {next_r, next_c};
                }
                
                // 继续沿着当前方向前进
                curr_r = next_r;
                curr_c = next_c;
            }
        };
        
        while (!forward_q.empty() && !backward_q.empty()) {
            // 从玩家位置扩展
            for (T level = static_cast<T>(forward_q.size()); level > 0; --level) {
                auto [r, c] = forward_q.front();
                forward_q.pop();
                
                // 对每个方向进行跳跃搜索
                for (const auto& dir : directions) {
                    auto [jump_r, jump_c] = jumpPoint(r, c, dir[0], dir[1], backward_visited);
                    
                    if (jump_r == r && jump_c == c) continue;
                    
                    if (backward_visited[jump_r][jump_c]) return true;
                    
                    if (!forward_visited[jump_r][jump_c]) {
                        forward_visited[jump_r][jump_c] = true;
                        forward_q.push({jump_r, jump_c});
                    }
                }
            }
            
            // 从箱子位置扩展（与上面类似）
            for (T level = static_cast<T>(backward_q.size()); level > 0; --level) {
                auto [r, c] = backward_q.front();
                backward_q.pop();
                
                for (const auto& dir : directions) {
                    auto [jump_r, jump_c] = jumpPoint(r, c, dir[0], dir[1], forward_visited);
                    
                    if (jump_r == r && jump_c == c) continue;
                    
                    if (forward_visited[jump_r][jump_c]) return true;
                    
                    if (!backward_visited[jump_r][jump_c]) {
                        backward_visited[jump_r][jump_c] = true;
                        backward_q.push({jump_r, jump_c});
                    }
                }
            }
        }
        
        return false;
    }

public:
    // 添加类型选择函数
    void initializeCoordType(const vector<vector<char>>& grid) {
        size_t rows = grid.size();
        size_t cols = grid[0].size();
        selectCoordType<T>(rows, cols);
    }

    string minPushBox(vector<vector<char>>& grid) {
        // 在开始处理前初始化坐标类型
        initializeCoordType(grid);
        // 清除旧的缓存
        clearCache();
        
        // 在开搜索之前先进行初始状态检查
        if (!isValidInitialState(grid)) {
            return "No solution!";
        }
        
        T n = static_cast<T>(grid.size());
        T m = static_cast<T>(grid[0].size());
        T player = 0;
        vector<T> boxes;
        unordered_set<State<T>, typename State<T>::Hash> visited;
        priority_queue<pair<State<T>, vector<char>>> q;

        initialize(grid, n, m, player, boxes);

        State<T> initial = {player, boxes, 0, 0};
        initial.g_score = 0;
        initial.f_score = calculateHeuristic(initial, grid, m);
        
        q.push({initial, {}});
        visited.insert(initial);

        while (!q.empty()) {
            auto [current, path] = q.top();
            q.pop();

            if (isGoalState(current, grid, m)) {
                return string(path.begin(), path.end());
            }

            expandStateAStar(current, n, m, grid, visited, q, path);
        }
        return "No solution!";
    }

private:
    void initialize(const vector<vector<char>>& grid, T n, T m, T& player, vector<T>& boxes) {
        for (T r = 0; r < n; ++r) {
            for (T c = 0; c < m; ++c) {
                if (grid[r][c] == 'S') {
                    player = toIndex(r, c, m);  // 玩家位置
                } else if (grid[r][c] == 'B' || grid[r][c] == 'R') {  // 处理初始地图中的箱子，包括在目标上箱子
                    boxes.push_back(toIndex(r, c, m));  // 所有箱子的位置
                }
            }
        }
        sort(boxes.begin(), boxes.end());  // 对箱子的位置排序，以便于状态压缩
    }

    bool isGoalState(const State<T>& state, const vector<vector<char>>& grid, T m) {
        for (T box : state.boxes) {
            auto [r, c] = toCoords(box, m);
            if (grid[r][c] != 'T' && grid[r][c] != 'R') {  // 箱子必须在目标位置（包括初始R位置）
                return false;
            }
        }
        return true;
    }

    int calculateHeuristic(const State<T>& state, const vector<vector<char>>& grid, T m) {
        int h_score = 0;
        vector<pair<T, T>> targets;
        
        // 收集所有目标位置
        for (T r = 0; r < grid.size(); ++r) {
            for (T c = 0; c < grid[0].size(); ++c) {
                if (grid[r][c] == 'T' || grid[r][c] == 'R') {
                    targets.push_back({r, c});
                }
            }
        }

        // 计算所有箱子到最近目标的曼哈顿距离之和
        for (T box : state.boxes) {
            if (box_to_target_distance_cache.find(box) == box_to_target_distance_cache.end()) {
                auto [box_r, box_c] = toCoords(box, m);
                int min_dist = INT_MAX;
                
                for (const auto& target : targets) {
                    int dist = abs(static_cast<int>(box_r) - static_cast<int>(target.first)) +
                              abs(static_cast<int>(box_c) - static_cast<int>(target.second));
                    min_dist = min(min_dist, dist);
                }
                box_to_target_distance_cache[box] = min_dist; // 缓存距离
            }
            h_score += box_to_target_distance_cache[box];
        }
        
        return h_score;
    }

    void updateHeuristicCache(T moved_box, [[maybe_unused]] const vector<vector<char>>& grid, T m) {
        // 更新移动箱子的距离缓存
        auto [box_r, box_c] = toCoords(moved_box, m);
        int min_dist = INT_MAX;
        for (const auto& target : cached_targets) {
            int dist = abs(static_cast<int>(box_r) - static_cast<int>(target.first)) +
                      abs(static_cast<int>(box_c) - static_cast<int>(target.second));
            min_dist = min(min_dist, dist);
        }
        box_to_target_distance_cache[moved_box] = min_dist;
    }

    void expandStateAStar(const State<T>& current, T n, T m,
                        const vector<vector<char>>& grid,
                        unordered_set<State<T>, typename State<T>::Hash>& visited,
                        priority_queue<pair<State<T>, vector<char>>>& q,
                        const vector<char>& path) {
        
        static vector<T> new_boxes;  // 静态分配避免重复创建
        new_boxes.reserve(current.boxes.size());
        
        auto [r, c] = toCoords(current.player, m);
        
        for (int i = 0; i < 4; ++i) {
            T new_r = safeAdd(r, directions[i][0]);
            T new_c = safeAdd(c, directions[i][1]);
            T new_player = toIndex(new_r, new_c, m);

            if (new_r >= n || new_c >= m || grid[new_r][new_c] == '#') {
                continue;
            }

            bool pushed_box = false;
            new_boxes = current.boxes;  // 重用预分配的vector
            
            for (T j = 0; j < new_boxes.size(); ++j) {
                if (new_boxes[j] == new_player) {
                    auto [box_r, box_c] = toCoords(new_boxes[j], m);
                    // 使用 safeAdd 来计算新的箱子位置
                    T box_new_r = safeAdd(box_r, directions[i][0]);
                    T box_new_c = safeAdd(box_c, directions[i][1]);
                    T new_box_pos = toIndex(box_new_r, box_new_c, m);

                    if (box_new_r >= n || box_new_c >= m || 
                        grid[box_new_r][box_new_c] == '#' ||
                        std::find(new_boxes.begin(), new_boxes.end(), new_box_pos) != new_boxes.end() ||
                        isDeadlock(box_new_r, box_new_c, grid)) {
                        pushed_box = false;
                        break;
                    }
                    new_boxes[j] = new_box_pos;
                    pushed_box = true;
                }
            }

            if (pushed_box) {
                sort(new_boxes.begin(), new_boxes.end());
                vector<char> new_path = path;  // 这里的复制是必要的
                new_path.push_back(numberToMove(i));
                
                State<T> new_state = {new_player, new_boxes, 0, current.g_score + 1};
                new_state.f_score = new_state.g_score + calculateHeuristic(new_state, grid, m);

                if (visited.find(new_state) == visited.end()) {
                    visited.insert(new_state);
                    q.push({new_state, new_path});
                }
            } else {
                if (std::find(current.boxes.begin(), current.boxes.end(), new_player) != current.boxes.end()) {
                    continue;
                }
                vector<char> new_path = path;  // 这里的复制是必要的
                new_path.push_back(numberToMove(i));
                
                State<T> new_state = {new_player, current.boxes, 0, current.g_score + 1};
                new_state.f_score = new_state.g_score + calculateHeuristic(new_state, grid, m);

                if (visited.find(new_state) == visited.end()) {
                    visited.insert(new_state);
                    q.push({new_state, new_path});
                }
            }
        }
    }

    bool isDeadlock(T box_r, T box_c, const vector<vector<char>>& grid) {
        // 初始化或更新缓存
        initializeCache(grid);
        
        // 使用缓存的死角网格和目标点
        vector<pair<T, T>> boxes;
        boxes.push_back({box_r, box_c});  // 只添加当前正在检查的箱子
        
        if (box_r >= grid.size() || box_c >= grid[0].size()) {
            return true;
        }
        
        T m = static_cast<T>(grid[0].size());
        
        if (grid[box_r][box_c] != 'T') {
            // 检查双箱子死锁
            vector<T> boxes;
            if (isDoubleBoxDeadlock(box_r, box_c, grid, boxes, m)) {
                return true;
            }

            // 检查角落死锁
            bool top_wall = (box_r == 0) || (grid[box_r - 1][box_c] == '#');
            bool bottom_wall = (box_r == grid.size() - 1) || (grid[box_r + 1][box_c] == '#');
            bool left_wall = (box_c == 0) || (grid[box_r][box_c - 1] == '#');
            bool right_wall = (box_c == grid[0].size() - 1) || (grid[box_r][box_c + 1] == '#');
            
            // 角落死锁
            if ((top_wall && left_wall) || (top_wall && right_wall) || 
                (bottom_wall && left_wall) || (bottom_wall && right_wall)) {
                return true;
            }

            // 检查边墙死锁
            if (top_wall || bottom_wall) {
                bool has_target = false;
                bool has_reachable_opening = false;
                
                if (box_r < grid.size()) {
                    // 检查该行是否有目标点
                    for (T c = 0; c < grid[0].size(); ++c) {
                        if (grid[box_r][c] == 'T') {
                            has_target = true;
                            break;
                        }
                    }
                    
                    // 只有在没有目标点的情况下才检查开孔
                    if (!has_target) {
                        // 检查是否有可达的开孔
                        for (T c = 0; c < grid[0].size(); ++c) {
                            if ((top_wall && box_r > 0 && grid[box_r-1][c] != '#') ||
                                (bottom_wall && box_r < grid.size()-1 && grid[box_r+1][c] != '#')) {
                                // 只要有开孔就认为是可行的，不再检查具体路径
                                has_reachable_opening = true;
                                break;
                            }
                        }
                        
                        // 只有在没有目标点且没有开孔时才判定为死锁
                        if (!has_reachable_opening) {
                            return true;
                        }
                    }
                }
            }
            
            // 查水平方向
            if (left_wall || right_wall) {
                bool has_target = false;
                bool has_reachable_opening = false;
                
                if (box_c < grid[0].size()) {
                    // 检查该列是否有目标点
                    for (T r = 0; r < grid.size(); ++r) {
                        if (grid[r][box_c] == 'T') {
                            has_target = true;
                            break;
                        }
                    }
                    
                    // 只有在没有目标点的情况下才检查开孔
                    if (!has_target) {
                        // 检查是否有可达的开孔
                        for (T r = 0; r < grid.size(); ++r) {
                            if ((left_wall && box_c > 0 && grid[r][box_c-1] != '#') ||
                                (right_wall && box_c < grid[0].size()-1 && grid[r][box_c+1] != '#')) {
                                // 只要有开孔就认为是可行的，不再检查具体路径
                                has_reachable_opening = true;
                                break;
                            }
                        }
                        
                        // 只有在没有目标点且没有开孔时才判定为死锁
                        if (!has_reachable_opening) {
                            return true;
                        }
                    }
                }
            }
        }
        
        return false;
    }

    bool checkBoxesToTargets(const vector<pair<T, T>>& boxes, 
                            const vector<pair<T, T>>& targets,
                            vector<vector<char>>& current_grid,
                            vector<vector<char>>& original_grid) {  // 添加原始地图参数
        
        // 首先处理墙角目标点
        for (T r = 0; r < current_grid.size(); ++r) {
            for (T c = 0; c < current_grid[0].size(); ++c) {
                if (current_grid[r][c] == 'Y') {
                    bool valid_target = false;
                    // 检查是否有箱子可以到达相邻的O点
                    for (const auto& box : boxes) {
                        for (const auto& dir : directions) {
                            T check_r = safeAdd(r, dir[0]);
                            T check_c = safeAdd(c, dir[1]);
                            
                            if (check_r < current_grid.size() && check_c < current_grid[0].size() && 
                                current_grid[check_r][check_c] == 'O') {
                                if (floodFill(box, current_grid, {check_r, check_c})) {
                                    valid_target = true;
                                    break;
                                }
                            }
                        }
                        if (valid_target) break;
                    }
                    
                    // 如果Y点无效，在两个地图中都移除该目标点
                    if (!valid_target) {
                        current_grid[r][c] = '.';
                        original_grid[r][c] = '.';
                    } else {
                        // 如果Y点有效，将其恢复为T
                        current_grid[r][c] = 'T';
                    }
                }
            }
        }

        // 然后检查所有目标点的可达性
        for (T r = 0; r < current_grid.size(); ++r) {
            for (T c = 0; c < current_grid[0].size(); ++c) {
                if (current_grid[r][c] == 'T') {
                    bool can_be_reached_by_box = false;
                    for (const auto& box : boxes) {
                        if (floodFill(box, current_grid, {r, c})) {
                            can_be_reached_by_box = true;
                            break;
                        }
                    }
                    if (!can_be_reached_by_box) {
                        current_grid[r][c] = '.';     // 修改临时地图中的目标点
                        original_grid[r][c] = '.';    // 同时修改原始地图中的目标点
                    }
                }
            }
        }

        // 最后检查每个箱子是否能到达至少一个有效目标点
        for (const auto& box : boxes) {
            bool can_reach_any_target = false;
            for (const auto& target : targets) {
                if (current_grid[target.first][target.second] == 'T' &&
                    floodFill(box, current_grid, target)) {
                    can_reach_any_target = true;
                    break;
                }
            }
            if (!can_reach_any_target) {
                return false;
            }
        }
        
        return true;
    }

    bool isValidInitialState(vector<vector<char>>& grid) {
        
        vector<pair<T, T>> boxes, targets, reached_targets;
        pair<T, T> player;
        bool player_found = false;
        T m = static_cast<T>(grid[0].size());
        
        // 收集所有位置信息
        for (T r = 0; r < grid.size(); ++r) {
            for (T c = 0; c < grid[0].size(); ++c) {
                if (grid[r][c] == 'S') {
                    if (player_found) return false;
                    player = {r, c};
                    player_found = true;
                } else if (grid[r][c] == 'B') {
                    boxes.push_back({r, c});
                } else if (grid[r][c] == 'T') {
                    targets.push_back({r, c});
                } else if (grid[r][c] == 'R') {
                    reached_targets.push_back({r, c});
                }   
            }
        } 
        
        if (!player_found) return false;
        
        // 查初始状态的死锁
        vector<T> box_indices;
        for (const auto& box : boxes) {
            box_indices.push_back(toIndex(box.first, box.second, m));
            // 检查每个箱子的初始位置是否已经死锁
            if (isDeadlock(box.first, box.second, grid)) {
                return false;
            }
        }
        
        // 检查双箱子死锁
        for (const auto& box : boxes) {
            if (isDoubleBoxDeadlock(box.first, box.second, grid, box_indices, m)) {
                return false;
            }
        }
        
        // 1. 检查S,T,B的通性（使用原始地图，不考虑死角）
        for (const auto& box : boxes) {
            if (!floodFill(player, grid, box)) {
                return false;
            }
        }
        for (const auto& target : targets) {
            if (!floodFill(player, grid, target)) {
                return false;
            }
        }
        
        // 2. 创建带死角标记的临时地图
        //修改查看T是否可以到达的逻辑。维持X的相关检测逻辑，新增概念Ytemp_grid[r][c] = 'Y'; 为所有墙角的目标点标记。
        //现在继续标注所有Y的非墙非X临近点O，利用checkBoxesToTargets检测如果O可以到达，则Y是有效T，否则Y不是有效点。
        vector<vector<char>> temp_grid = grid;
        for (T r = 0; r < grid.size(); ++r) {
            for (T c = 0; c < grid[0].size(); ++c) {
                if (grid[r][c] != '#') {
                    bool top_wall = (r == 0) || (grid[r-1][c] == '#');
                    bool bottom_wall = (r == grid.size()-1) || (grid[r+1][c] == '#');
                    bool left_wall = (c == 0) || (grid[r][c-1] == '#');
                    bool right_wall = (c == grid[0].size()-1) || (grid[r][c+1] == '#');
                    
                    if ((top_wall && left_wall) || (top_wall && right_wall) || 
                        (bottom_wall && left_wall) || (bottom_wall && right_wall)) {
                        if (grid[r][c] == 'T') {
                            temp_grid[r][c] = 'Y';  // 墙角目标点标记
                            for (const auto& dir : directions) {
                                T new_r = safeAdd(r, dir[0]);
                                T new_c = safeAdd(c, dir[1]);
                                if (new_r < grid.size() && new_c < grid[0].size() && 
                                    temp_grid[new_r][new_c] != '#' && 
                                    temp_grid[new_r][new_c] != 'X' &&
                                    temp_grid[new_r][new_c] != 'Y') {
                                    temp_grid[new_r][new_c] = 'O';
                                }
                            }
                        } else {  
                            temp_grid[r][c] = 'X'; // 墙角非空目标点标记为死角
                        }
                    }
                }
            }
        }

        // if (!temp_grid.empty()) {
        //     for (size_t i = 0; i < temp_grid.size(); i++) {
        //         for (size_t j = 0; j < temp_grid[i].size(); j++) {
        //             std::cout << temp_grid[i][j];
        //         }   
        //         std::cout << std::endl;
        //     }
        // }
        // 3. 使用带死角的临时地图检查箱子到目标点的可达性
        if (!checkBoxesToTargets(boxes, targets, temp_grid, grid)) {
            return false;
        }

        // if (!grid.empty()) {
        //     for (size_t i = 0; i < grid.size(); i++) {
        //         for (size_t j = 0; j < grid[i].size(); j++) {
        //             std::cout << grid[i][j];
        //         }   
        //         std::cout << std::endl;
        //     }
        // }
        // 重新统计有效目标点数量
        T valid_target_count = 0;
        for (T r = 0; r < grid.size(); ++r) {
            for (T c = 0; c < grid[0].size(); ++c) {
                if (grid[r][c] == 'T') {
                    valid_target_count++;
                }
            }
        }
        
        return boxes.size() <= valid_target_count;
    }

    bool isDoubleBoxDeadlock(T box_r, T box_c, const vector<vector<char>>& grid, const vector<T>& boxes, T m) {
        // 如果当前位置是目标点，则不是死锁
        if (grid[box_r][box_c] == 'T' || grid[box_r][box_c] == 'R') {
            return false;
        }

        // 检查水平方向的双箱子死锁
        if (box_c > 0 && box_c < grid[0].size() - 1) {
            T left_pos = toIndex(box_r, static_cast<T>(static_cast<size_t>(box_c) - 1), m);
            bool has_left_box = std::find(boxes.begin(), boxes.end(), left_pos) != boxes.end();
            T right_pos = toIndex(box_r, static_cast<T>(static_cast<size_t>(box_c) + 1), m);
            bool has_right_box = std::find(boxes.begin(), boxes.end(), right_pos) != boxes.end();

            if (has_left_box || has_right_box) {
                bool vertical_walls = (box_r == 0 || grid[box_r - 1][box_c] == '#') &&
                                    (box_r == grid.size() - 1 || grid[box_r + 1][box_c] == '#');

                if (vertical_walls) {
                    if (has_left_box && grid[box_r][box_c - 1] != 'T' && grid[box_r][box_c - 1] != 'R') {
                        bool left_box_trapped = (box_r == 0 || grid[box_r - 1][box_c - 1] == '#') &&
                                              (box_r == grid.size() - 1 || grid[box_r + 1][box_c - 1] == '#');
                        if (left_box_trapped) return true;
                    }
                    if (has_right_box && grid[box_r][box_c + 1] != 'T' && grid[box_r][box_c + 1] != 'R') {
                        bool right_box_trapped = (box_r == 0 || grid[box_r - 1][box_c + 1] == '#') &&
                                               (box_r == grid.size() - 1 || grid[box_r + 1][box_c + 1] == '#');
                        if (right_box_trapped) return true;
                    }
                } else {
                    // 检查玩家是否可以到达箱子的上下任意一侧
                    vector<vector<char>> temp_grid = grid;
                    // 将所有箱子标记为墙，除了当前检查的箱子
                    
                    bool can_reach_vertical = false;
                    // 检查上侧
                    if (box_r > 0 && temp_grid[box_r-1][box_c] != '#') {
                        for (T r = 0; r < grid.size(); ++r) {
                            for (T c = 0; c < grid[0].size(); ++c) {
                                if (temp_grid[r][c] == 'S') {
                                    if (floodFill({r, c}, temp_grid, {box_r-1, box_c})) {
                                        can_reach_vertical = true;
                                        break;
                                    }
                                }
                            }
                            if (can_reach_vertical) break;
                        }
                    }
                    // 检查下侧
                    if (!can_reach_vertical && box_r < grid.size()-1 && temp_grid[box_r+1][box_c] != '#') {
                        for (T r = 0; r < grid.size(); ++r) {
                            for (T c = 0; c < grid[0].size(); ++c) {
                                if (temp_grid[r][c] == 'S') {
                                    if (floodFill({r, c}, temp_grid, {box_r+1, box_c})) {
                                        can_reach_vertical = true;
                                        break;
                                    }
                                }
                            }
                            if (can_reach_vertical) break;
                        }
                    }
                    
                    if (!can_reach_vertical) return true;
                }
            }
        }

        // 检查垂直方向的双箱子死锁
        if (box_r > 0 && box_r < grid.size() - 1) {
            T up_pos = toIndex(static_cast<T>(static_cast<size_t>(box_r) - 1), box_c, m);
            bool has_up_box = std::find(boxes.begin(), boxes.end(), up_pos) != boxes.end();
            T down_pos = toIndex(static_cast<T>(static_cast<size_t>(box_r) + 1), box_c, m);
            bool has_down_box = std::find(boxes.begin(), boxes.end(), down_pos) != boxes.end();

            if (has_up_box || has_down_box) {
                bool horizontal_walls = (box_c == 0 || grid[box_r][box_c - 1] == '#') &&
                                      (box_c == grid[0].size() - 1 || grid[box_r][box_c + 1] == '#');

                if (horizontal_walls) {
                    if (has_up_box && grid[box_r - 1][box_c] != 'T' && grid[box_r - 1][box_c] != 'R') {
                        bool up_box_trapped = (box_c == 0 || grid[box_r - 1][box_c - 1] == '#') &&
                                            (box_c == grid[0].size() - 1 || grid[box_r - 1][box_c + 1] == '#');
                        if (up_box_trapped) return true;
                    }
                    if (has_down_box && grid[box_r + 1][box_c] != 'T' && grid[box_r + 1][box_c] != 'R') {
                        bool down_box_trapped = (box_c == 0 || grid[box_r + 1][box_c - 1] == '#') &&
                                              (box_c == grid[0].size() - 1 || grid[box_r + 1][box_c + 1] == '#');
                        if (down_box_trapped) return true;
                    }
                } else {
                    // 检查玩家是否可以到达箱子的左右任意一侧
                    vector<vector<char>> temp_grid = grid;
                    
                    bool can_reach_horizontal = false;
                    // 检查左侧
                    if (box_c > 0 && temp_grid[box_r][box_c-1] != '#') {
                        for (T r = 0; r < grid.size(); ++r) {
                            for (T c = 0; c < grid[0].size(); ++c) {
                                if (temp_grid[r][c] == 'S') {
                                    if (floodFill({r, c}, temp_grid, {box_r, box_c-1})) {
                                        can_reach_horizontal = true;
                                        break;
                                    }
                                }
                            }
                            if (can_reach_horizontal) break;
                        }
                    }
                    // 检查右侧
                    if (!can_reach_horizontal && box_c < grid[0].size()-1 && temp_grid[box_r][box_c+1] != '#') {
                        for (T r = 0; r < grid.size(); ++r) {
                            for (T c = 0; c < grid[0].size(); ++c) {
                                if (temp_grid[r][c] == 'S') {
                                    if (floodFill({r, c}, temp_grid, {box_r, box_c+1})) {
                                        can_reach_horizontal = true;
                                        break;
                                    }
                                }
                            }
                            if (can_reach_horizontal) break;
                        }
                    }
                    
                    if (!can_reach_horizontal) return true;
                }
            }
        }

        return false;
    }

    char numberToMove(int dir) {
        static const char moves[4] = {'U', 'D', 'L', 'R'};
        return moves[dir];
    }

};

// 修改 solve 函数以使用模板
string solve(vector<string>& grid) {
    // 根据网格大小择合适的类
    size_t rows = grid.size();
    size_t cols = grid[0].size();
    size_t total_size = rows * cols;
    
    if (total_size <= CoordTraits<uint8_t>::max_size) {
        Solution<uint8_t> sol;
        vector<vector<char>> charGrid(rows, vector<char>(cols));
        for (size_t i = 0; i < rows; ++i) {
            for (size_t j = 0; j < cols; ++j) {
                charGrid[i][j] = grid[i][j];
            }
        }
        return sol.minPushBox(charGrid);
    } else if (total_size <= CoordTraits<uint16_t>::max_size) {
        Solution<uint16_t> sol;
        vector<vector<char>> charGrid(rows, vector<char>(cols));
        for (size_t i = 0; i < rows; ++i) {
            for (size_t j = 0; j < cols; ++j) {
                charGrid[i][j] = grid[i][j];
            }
        }
        return sol.minPushBox(charGrid);
    } else {
        Solution<uint32_t> sol;
        vector<vector<char>> charGrid(rows, vector<char>(cols));
        for (size_t i = 0; i < rows; ++i) {
            for (size_t j = 0; j < cols; ++j) {
                charGrid[i][j] = grid[i][j];
            }
        }
        return sol.minPushBox(charGrid);
    }
}


void read_map(std::vector<std::string> &grid) {
    std::size_t cols, rows;
    
    // 关闭同步
    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
    
    cin >> cols >> rows;
    grid.resize(rows);
    
    // 预分配空间
    for (auto& row : grid) {
        row.reserve(cols);
    }
    
    // 直接读取
    for (auto& row : grid) {
        cin >> row;
    }
}
// For big cases, paste your answers here (i.e. replace "ans for big 1" with your answer)
// Do not remove the first element, it should be left blank.
// NOTE: Ensure the order is correct!
// Your answer should look like "UUDDLLRR..."
const vector<string> answers = {
    "__leave_this_blank__", 
};

// Don't modify this.
string print_answer(int index) {
    if (index < 1 || index >= static_cast<int>(answers.size())) {
        return "No solution!";
    }
    return answers[static_cast<size_t>(index)];
}
