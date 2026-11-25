# ERDOS-64 Wave 2 Agent #3 — Exact Exhaustive 2-Port & 3-Port Gadget Bounds

Exact, lossless OpenMP-parallelized C++ enumerator for connected power-free ($C_4, C_8, C_{16}$-free) cubic 2-port and 3-port gadgets, extending Wave 1 bounds beyond the Ducoffe–Dumitru (2026) SOTA ($n \le 48$ cubic, $n \le 40$ general):

- General cubic 2-port gadgets at $n = 24$ $\implies$ if 0 exist, `C-T-2` requires $|A|, |B| \ge 26 \implies |V(G)| \ge 52$ (surpassing $n \le 48$).
- Triangle-free cubic 2-port gadgets at $n = 26$ $\implies$ if 0 exist, `C-N-2` requires $|A|, |B| \ge 28 \implies |V(G)| \ge 56$.
- Triangle-free cubic 3-port gadgets at $n = 23$ $\implies$ if 0 exist, `C-N-3` requires $|A|, |B| \ge 25 \implies |V(G)| \ge 50$ (surpassing $n \le 48$) and `S-N-2` requires $|V(G)| \ge 53$.
- General cubic 3-port gadgets at $n = 21$ (extending the $n \le 19$ census).
