#include "sokoban.hpp"
#include <vector>
#include <string>

int main() {
    std::vector<std::string> grid;
    read_map(grid);
    
    // 打印地图
    if (!grid.empty()) {
        for (size_t i = 0; i < grid.size(); i++) {
            std::cout << grid[i];  // 打印当前行
            std::cout << std::endl;  // 每行后都输出换行符
        }
    }
    
    std::cout << solve(grid) << std::endl;
    return 0;
}
