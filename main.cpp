#include <iostream>
#include <string>
#include <array>
#include <memory>
#include <filesystem>

namespace fs = std::filesystem;

int main() {
    std::string test_target = "test_hyper_apex_level_13.py"; 
    std::cout << "=== RUNNING STANDALONE HIGH-VOLUME LEAN 4 SYNTHESIS ===" << std::endl;
    
    if (!fs::exists(test_target)) {
        std::cerr << "[ERROR] Level 13 engine script missing: " << test_target << std::endl;
        return 1;
    }
    
    std::string command = "python3 -u " + test_target;
    std::array<char, 512> buffer;
    
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(command.c_str(), "r"), pclose);
    if (!pipe) {
        std::cerr << "[CRITICAL ERROR] Failed to allocate system process handles." << std::endl;
        return 1;
    }

    std::cout << "=== LEVEL 13 PIPELINE STREAM OPEN ===" << std::endl;
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        std::cout << "[L13_RUN]: " << buffer.data();
    }
    std::cout << "====================================" << std::endl;
    return 0;
}
