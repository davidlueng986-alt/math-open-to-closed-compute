#include "engine.hpp"

int main(int argc, char **argv) {
    if (argc != 5) {
        cerr << "usage: search both|extend57 SEED COARSE_STEPS PHASE_STEPS\n";
        return 2;
    }
    string mode = argv[1];
    if (mode != "both" && mode != "extend57")
        return 2;
    Engine e(stoul(argv[2]), mode == "extend57");
    e.load();
    e.coarseSearch(stoi(argv[3]));
    e.coarseRepair(65000);
    e.phaseSearch(stoi(argv[4]));
    e.phaseRepair(65000);
    e.result();
}
