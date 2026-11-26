#include <algorithm>
#include <fstream>
#include <iostream>
#include <vector>

using Matrix = std::vector<std::vector<int>>;
constexpr int selected = 600, reserve = 596, height = selected + reserve, total_units = 29;

template<int prime>
int residue(int x) {
    const int value = x % prime;
    return value < 0 ? value + prime : value;
}

template<int prime>
std::vector<int> reduce(Matrix& matrix) {
    for (auto& row : matrix)
        for (int& value : row) value = residue<prime>(value);
    std::vector<int> pivots;
    for (int j = 0; j < int(matrix.front().size()) && pivots.size() < matrix.size(); ++j) {
        const int rank = pivots.size();
        int pivot = rank;
        while (pivot < int(matrix.size()) && matrix[pivot][j] == 0) ++pivot;
        if (pivot == int(matrix.size())) continue;
        std::swap(matrix[rank], matrix[pivot]);
        auto& line = matrix[rank];
        int inverse = 1;
        while (inverse * line[j] % prime != 1) ++inverse;
        for (int k = j; k < int(line.size()); ++k) line[k] = line[k] * inverse % prime;
        for (int i = 0; i < int(matrix.size()); ++i) {
            auto& other = matrix[i];
            const int scale = other[j];
            if (i == rank || scale == 0) continue;
            for (int k = j; k < int(line.size()); ++k)
                other[k] = (other[k] + (prime - scale) * line[k]) % prime;
        }
        pivots.push_back(j);
    }
    return pivots;
}

template<int prime>
Matrix null_basis(Matrix& matrix) {
    const auto pivots = reduce<prime>(matrix);
    const int width = matrix.front().size();
    Matrix basis(width, std::vector<int>(width - pivots.size()));
    int index = 0;
    for (int j = 0; j < width; ++j) {
        if (std::binary_search(pivots.begin(), pivots.end(), j)) continue;
        basis[j][index] = 1;
        for (int i = 0; i < int(pivots.size()); ++i)
            basis[pivots[i]][index] = residue<prime>(-matrix[i][j]);
        ++index;
    }
    return basis;
}

template<int prime>
bool check(const Matrix& input, const std::vector<int>& signs, int units) {
    Matrix matrix, image;
    for (const auto& row : input) {
        matrix.emplace_back(row.begin(), row.begin() + selected + units);
        image.emplace_back(row.begin() + selected, row.begin() + selected + units);
    }
    if (int(reduce<prime>(image).size()) != units) return false;
    const Matrix basis = null_basis<prime>(matrix);
    const int dimension = basis.front().size();
    if (dimension != units + 2) return false;

    Matrix transposed(dimension, std::vector<int>(selected));
    for (int i = 0; i < selected; ++i)
        for (int j = 0; j < dimension; ++j) transposed[j][i] = basis[i][j];
    const auto independent = reduce<prime>(transposed);
    if (int(independent.size()) != dimension) return false;

    // Invert the independent top-coordinate restriction of the kernel basis.
    Matrix inverse(dimension, std::vector<int>(2 * dimension));
    for (int i = 0; i < dimension; ++i) {
        std::copy(basis[independent[i]].begin(), basis[independent[i]].end(), inverse[i].begin());
        inverse[i][dimension + i] = 1;
    }
    const auto inverse_pivots = reduce<prime>(inverse);
    if (int(inverse_pivots.size()) != dimension || inverse_pivots.back() != dimension - 1)
        return false;

    const int monomials = dimension * (dimension + 1) / 2;
    Matrix quadratic(selected, std::vector<int>(monomials));
    for (int i = 0; i < selected; ++i) {
        std::vector<int> coefficients(dimension);
        for (int j = 0; j < dimension; ++j) {
            int sum = 0;
            for (int k = 0; k < dimension; ++k) sum += basis[i][k] * inverse[k][dimension + j];
            coefficients[j] = residue<prime>(sum * signs[independent[j]]);
        }
        // Each a_i is either 0 or b_i, and the independent x_j are Boolean.
        // Expand a_i^2 - b_i a_i with x_j^2 replaced by x_j.
        auto& row = quadratic[i];
        int column = dimension;
        for (int j = 0; j < dimension; ++j) {
            row[j] = coefficients[j] * (coefficients[j] - signs[i]);
            for (int k = j + 1; k < dimension; ++k)
                row[column++] = 2 * coefficients[j] * coefficients[k];
        }
    }
    const auto rank = reduce<prime>(quadratic).size();
    if (int(rank) != monomials) return false;
    std::cout << units << " reserve axes, F" << prime << ": " << dimension
              << " Boolean coordinates, full quadratic rank " << rank << '/' << monomials
              << ", full unit-image rank\n";
    return true;
}

template<int prime>
bool check_crt(const Matrix& source, std::ostream& output) {
    Matrix matrix;
    matrix.reserve(height);
    for (const auto& row : source) {
        matrix.emplace_back(row.begin() + selected, row.end());
        matrix.back().insert(matrix.back().end(), row.begin(), row.begin() + selected);
    }

    // Put the reserve pivots first so the reduced rows give r and the two checks on a.
    const auto pivots = reduce<prime>(matrix);
    if (pivots.size() != 598 || pivots[reserve-1] != reserve-1) return false;
    Matrix chosen;
    for (int i = 0; i < int(pivots.size()); ++i)
        chosen.emplace_back(matrix[i].begin() + reserve, matrix[i].end());
    if (reduce<prime>(chosen).size() != 598) return false;

    for (int i = 0; i < int(pivots.size()); ++i)
        for (int j = reserve; j < height; ++j) output.put(static_cast<char>(matrix[i][j]));
    std::cout << "F" << prime << " source ranks X/V/A 598/596/598; "
              << "two chosen checks and unique reserve residues\n";
    return bool(output);
}

int main(int argc, char** argv) {
    if (argc != 2) return 1;
    std::vector<int> signs(selected);
    for (int& value : signs) std::cin >> value;
    Matrix input(height, std::vector<int>(selected + total_units));
    for (auto& row : input)
        for (int& value : row) std::cin >> value;
    if (!std::cin || !std::all_of(signs.begin(), signs.end(), [](int x) { return x == 1 || x == -1; }))
        return 1;
    for (int units : {15, 19, 29})
        if (!check<13>(input, signs, units) || !check<23>(input, signs, units)) return 2;

    Matrix source(height, std::vector<int>(height));
    for (int i = 0; i < height; ++i) {
        std::copy_n(input[i].begin(), selected, source[i].begin());
        for (int j = selected; j < height; ++j) std::cin >> source[i][j];
    }
    if (!std::cin) return 3;
    std::ofstream output(argv[1], std::ios::binary);
    if (!check_crt<13>(source, output) || !check_crt<23>(source, output)) return 4;
}
