#include <iostream>
#include <string>
#include <array>
#include <memory>
#include <filesystem>

namespace fs = std::filesystem;

int main() {
    std::string test_target = "aci_system_v2_core.py"; 
    std::cout << "=== RUNNING ULTIMATE PEAK: HYPER-APEX LEVEL 23 UNCHAINED CONSOLE ===" << std::endl;
    
    if (!fs::exists(test_target)) {
        std::cerr << "[ERROR] Upgraded V2 engine script missing: " << test_target << std::endl;
        return 1;
    }
    
    // Natively executing via standard shell system wrappers to preserve active bi-directional stdin streams
    std::string run_cmd = "python3 -u " + test_target;
    std::system(run_cmd.c_str());

    return 0;
}
