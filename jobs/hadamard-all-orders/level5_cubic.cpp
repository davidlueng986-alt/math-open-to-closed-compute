#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>

namespace {
constexpr int order = 10;
using Graph = std::array<unsigned, order>;

unsigned examined = 0;
unsigned even_edge_triangles = 0;
unsigned small_square_rank = 0;
unsigned petersen_type = 0;

int rank_five(const Graph& graph) {
    std::array<std::array<int, order>, order> matrix{};
    for (int i = 0; i < order; ++i) {
        for (int j = 0; j < order; ++j) {
            const int adjacency = (graph[i] >> j) & 1U;
            matrix[i][j] = (2 * (i == j) + adjacency + 4) % 5;
        }
    }
    constexpr std::array inverse{0, 1, 3, 2, 4};
    int rank = 0;
    for (int j = 0; j < order; ++j) {
        int pivot = rank;
        while (pivot < order && !matrix[pivot][j]) ++pivot;
        if (pivot == order) continue;
        std::swap(matrix[rank], matrix[pivot]);
        const int scale = inverse[matrix[rank][j]];
        for (int i = rank + 1; i < order; ++i) {
            const int coefficient = matrix[i][j] * scale % 5;
            for (int k = j; k < order; ++k) {
                matrix[i][k] = (matrix[i][k] + 20 - coefficient * matrix[rank][k]) % 5;
            }
        }
        ++rank;
    }
    return rank;
}

void check_graph(const Graph& graph) {
    ++examined;
    bool petersen = true;
    for (int i = 0; i < order; ++i) {
        for (int j = i + 1; j < order; ++j) {
            const int common = std::popcount(graph[i] & graph[j]);
            const bool edge = (graph[i] >> j) & 1U;
            if (edge && common % 2 != 0) return;
            if (common != !edge) petersen = false;
        }
    }
    ++even_edge_triangles;
    if (rank_five(graph) > 6) return;
    ++small_square_rank;
    if (petersen) ++petersen_type;
}

void extend(Graph& graph, int vertex);

void choose_neighbors(Graph& graph, int vertex, int candidate, int remaining) {
    if (remaining == 0) {
        extend(graph, vertex + 1);
        return;
    }
    for (int next = candidate; next <= order - remaining; ++next) {
        if (std::popcount(graph[next]) >= 3) continue;
        graph[vertex] |= 1U << next;
        graph[next] |= 1U << vertex;
        choose_neighbors(graph, vertex, next + 1, remaining - 1);
        graph[vertex] ^= 1U << next;
        graph[next] ^= 1U << vertex;
    }
}

void extend(Graph& graph, int vertex) {
    if (vertex == order) {
        check_graph(graph);
        return;
    }
    choose_neighbors(graph, vertex, vertex + 1, 3 - std::popcount(graph[vertex]));
}
}

int main() {
    Graph graph{};
    graph[0] = 0b1110;
    for (int i = 1; i <= 3; ++i) graph[i] = 1;
    extend(graph, 1);
    std::cout << "level5-cubic graphs=" << examined
              << " even-edge-triangles=" << even_edge_triangles
              << " square-rank<=6=" << small_square_rank
              << " petersen-type=" << petersen_type << '\n';
    if (examined != 133105 || even_edge_triangles != 21805 ||
        small_square_rank != 360 || petersen_type != small_square_rank) {
        return 1;
    }
    return 0;
}
