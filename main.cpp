#include <iostream>
#include <string>
#include <array>
#include <memory>
#include <filesystem>

namespace fs = std::filesystem;

int main() {
    std::string test_target = "test_hyper_apex_level_22.py"; 
    std::cout << "=== RUNNING THE UNCHARTED TIER: ACI SYSTEM V2 INTERACTIVE FABRICATOR ===" << std::endl;
    
    if (!fs::exists(test_target)) {
        std::cerr << "[ERROR] Level 22 engine script missing: " << test_target << std::endl;
        return 1;
    }
    
    std::string command = "python3 -u " + test_target;
    std::array<char, 512> buffer_arr;
    
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(command.c_str(), "r"), pclose);
    if (!pipe) {
        std::cerr << "[CRITICAL ERROR] Failed to allocate system process handles." << std::endl;
        return 1;
    }

    std::cout << "=== LEVEL 22 PIPELINE STREAM OPEN ===" << std::endl;
    while (fgets(buffer_arr.data(), buffer_arr.size(), pipe.get()) != nullptr) {
        std::cout << "[L22_RUN]: " << buffer_arr.data();
    }
    std::cout << "====================================" << std::endl;
    return 0;
}
