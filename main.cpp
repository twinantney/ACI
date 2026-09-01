#include <iostream>
#include <string>
#include <array>
#include <memory>
#include <fstream>
#include <filesystem>

namespace fs = std::filesystem;

int main() {
    std::string target = "PrimeRuntimeV4_backup.py";
    std::string log_file = "production_telemetry.log";
    
    std::cout << "=== ACI MASTER SYSTEM RUNTIME CORE COUPLING ===" << std::endl;
    
    if (!fs::exists(target)) {
        std::cerr << "[CRITICAL ERROR] Target runtime file not found: " << target << std::endl;
        return 1;
    }
    
    std::cout << "[ORCHESTRATOR] Operational core verified. Opening log stream: " << log_file << std::endl;
    
    // Initialize file write stream
    std::ofstream logger(log_file, std::ios::app);
    if (!logger.is_open()) {
        std::cerr << "[WARNING] Failed to open local log file for writing." << std::endl;
    }

    std::string command = "python3 -u " + target;
    std::array<char, 512> buffer;
    
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(command.c_str(), "r"), pclose);
    if (!pipe) {
        std::cerr << "[CRITICAL ERROR] Failed to allocate system process handles." << std::endl;
        return 1;
    }

    std::cout << "=== ACTIVE OPERATIONAL PIPELINE ROUTING ===" << std::endl;
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        std::string log_line = buffer.data();
        
        // Output cleanly to standard console
        std::cout << "[ACI_RUN]: " << log_line;
        
        // Write instantly to disk file if open
        if (logger.is_open()) {
            logger << "[ACI_RUN]: " << log_line;
            logger.flush();
        }
    }
    std::cout << "===========================================" << std::endl;
    std::cout << "[ORCHESTRATOR] Subprocess loop terminated cleanly." << std::endl;

    if (logger.is_open()) logger.close();
    return 0;
}
