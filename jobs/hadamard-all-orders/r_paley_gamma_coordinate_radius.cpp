#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <string_view>
#include <vector>

using Row = std::vector<int>;
using Matrix = std::vector<Row>;
constexpr int selected = 600, reserve_count = 596, height = selected + reserve_count;
constexpr int old_count = 15, units_count = 29, boolean_count = 31, field = 13, d = 299;
constexpr int y_dimension = boolean_count + 2;

template<int p>
int residue(int x) {
    const int value = x % p;
    return value < 0 ? value + p : value;
}

template<int p>
constexpr auto inverses() {
    std::array<int, p> output{};
    for (int i = 1; i < p; ++i)
        for (int j = 1; j < p; ++j)
            if (i*j % p == 1) output[i] = j;
    return output;
}

template<int p>
Row reduce(Matrix& matrix, bool full = true) {
    constexpr auto inverse = inverses<p>();
    for (auto& row : matrix)
        for (int& value : row) value = residue<p>(value);
    Row pivots;
    for (int j = 0; j < int(matrix[0].size()) && pivots.size() < matrix.size(); ++j) {
        const int rank = pivots.size();
        int pivot = rank;
        while (pivot < int(matrix.size()) && matrix[pivot][j] == 0) ++pivot;
        if (pivot == int(matrix.size())) continue;
        auto& line = matrix[rank];
        std::swap(line, matrix[pivot]);
        const int factor = inverse[line[j]];
        for (int k = j; k < int(line.size()); ++k) line[k] = line[k] * factor % p;
        for (int i = full ? 0 : rank+1; i < int(matrix.size()); ++i) {
            auto& other = matrix[i];
            const int scale = other[j];
            if (i == rank || scale == 0) continue;
            other[j] = 0;
            for (int k = j+1; k < int(line.size()); ++k)
                other[k] = (other[k] + (p-scale)*line[k]) % p;
        }
        pivots.push_back(j);
    }
    return pivots;
}

Matrix transpose(const Matrix& matrix) {
    Matrix output(matrix[0].size(), Row(matrix.size()));
    for (int i = 0; i < int(matrix.size()); ++i)
        for (int j = 0; j < int(matrix[i].size()); ++j) output[j][i] = matrix[i][j];
    return output;
}

template<int p>
int inner(const Row& a, const Row& b) {
    return residue<p>(std::inner_product(a.begin(), a.end(), b.begin(), 0));
}

template<int p>
Matrix multiply(const Matrix& a, const Matrix& b) {
    Matrix output(a.size(), Row(b[0].size()));
    const Matrix columns = transpose(b);
    for (int i = 0; i < int(a.size()); ++i)
        for (int j = 0; j < int(columns.size()); ++j) output[i][j] = inner<p>(a[i], columns[j]);
    return output;
}

template<int p>
Matrix kernel_rows(Matrix matrix) {
    const auto pivots = reduce<p>(matrix);
    Matrix output;
    for (int column = 0; column < int(matrix[0].size()); ++column) {
        if (std::binary_search(pivots.begin(), pivots.end(), column)) continue;
        Row vector(matrix[0].size());
        vector[column] = 1;
        for (int i = 0; i < int(pivots.size()); ++i)
            vector[pivots[i]] = residue<p>(-matrix[i][column]);
        output.push_back(vector);
    }
    return output;
}

template<int p>
Matrix reserve_first(const Matrix& source) {
    Matrix result;
    for (const auto& row : source) {
        result.emplace_back(row.begin()+selected, row.end());
        result.back().insert(result.back().end(), row.begin(), row.begin()+selected);
    }
    const auto pivots = reduce<p>(result);
    if (pivots.size() != reserve_count+2 || pivots[reserve_count-1] != reserve_count-1) return {};
    result.resize(pivots.size());
    return result;
}

struct Features {
    Matrix top;
    Matrix left;
    Matrix images;
    std::vector<Matrix> projected;
};

Features axis_features(const Matrix& reduced_source, const Matrix& units, const Row& b) {
    Matrix reverse;
    for (const auto& row : reduced_source) {
        reverse.emplace_back(row.begin()+reserve_count, row.end());
        reverse.back().insert(reverse.back().end(), row.begin(), row.begin()+reserve_count);
    }
    const auto chosen_pivots = reduce<field>(reverse);
    if (chosen_pivots.size() != 598 || chosen_pivots.back() >= selected) return {};
    Matrix top_map(selected, Row(reserve_count));
    Matrix raw_top(selected, Row(boolean_count));
    for (int i = 0; i < int(chosen_pivots.size()); ++i) {
        const int target = chosen_pivots[i];
        for (int j = 0; j < reserve_count; ++j) top_map[target][j] = residue<field>(-reverse[i][selected+j]);
        for (int j = 0; j < units_count; ++j) raw_top[target][j] = inner<field>(top_map[target], units[j]);
    }
    int free = units_count;
    for (int j = 0; j < selected; ++j) {
        if (std::binary_search(chosen_pivots.begin(), chosen_pivots.end(), j)) continue;
        raw_top[j][free] = 1;
        for (int i = 0; i < int(chosen_pivots.size()); ++i)
            raw_top[chosen_pivots[i]][free] = residue<field>(-reverse[i][j]);
        ++free;
    }
    Matrix transposed = transpose(raw_top);
    const auto boolean_pivots = reduce<field>(transposed);
    if (free != boolean_count || boolean_pivots.size() != boolean_count) return {};
    Matrix inverse(boolean_count, Row(2*boolean_count));
    for (int i = 0; i < boolean_count; ++i) {
        std::copy(raw_top[boolean_pivots[i]].begin(), raw_top[boolean_pivots[i]].end(), inverse[i].begin());
        inverse[i][boolean_count+i] = b[boolean_pivots[i]];
    }
    const auto inverse_pivots = reduce<field>(inverse);
    if (inverse_pivots.size() != boolean_count || inverse_pivots.back() != boolean_count-1) return {};
    for (auto& row : inverse) row.erase(row.begin(), row.begin()+boolean_count);
    Matrix top = multiply<field>(raw_top, inverse);
    Matrix fixed;
    for (int pivot : boolean_pivots) {
        fixed.push_back(top_map[pivot]);
        for (int& x : fixed.back()) x *= b[pivot];
    }
    const Matrix removed = multiply<field>(top, fixed);
    Matrix original;
    for (int j = 0; j < selected; ++j) {
        for (int g = 0; g < reserve_count; ++g) top_map[j][g] = residue<field>(top_map[j][g]-removed[j][g]);
        if (std::binary_search(boolean_pivots.begin(), boolean_pivots.end(), j)) {
            if (std::any_of(top_map[j].begin(), top_map[j].end(), [](int x){return x != 0;})) return {};
            continue;
        }
        Row monomials;
        for (int x : top[j]) monomials.push_back(x*(x-b[j]));
        for (int i = 0; i < boolean_count; ++i)
            for (int k = i+1; k < boolean_count; ++k) monomials.push_back(2*top[j][i]*top[j][k]);
        original.push_back(monomials);
    }
    Matrix left = kernel_rows<field>(transpose(original));
    if (left.size() != 73) return {};
    for (int pivot : boolean_pivots)
        for (auto& row : left) row.insert(row.begin()+pivot, 0);
    const Matrix left_columns = transpose(left);
    const Matrix images = transpose(top_map);
    std::vector<Matrix> projected;
    for (const Row& image : images) {
        Matrix terms(y_dimension, Row(selected));
        for (int j = 0; j < selected; ++j) {
            terms[0][j] = residue<field>(-b[j]*image[j]);
            terms[1][j] = image[j]*image[j] % field;
            for (int i = 0; i < boolean_count; ++i) terms[2+i][j] = 2*image[j]*top[j][i] % field;
        }
        projected.push_back(multiply<field>(terms, left_columns));
    }
    return {top, left, images, projected};
}

bool check_first_pivot(const Features& features, const Matrix& old, const Row& positions) {
    const Row& b = old[0];
    const int pivot = positions[0];
    const auto& first = features.projected[pivot];
    for (int i = 0; i < selected; ++i) {
        const int all = std::accumulate(features.top[i].begin(), features.top[i].end(), 0);
        if (features.images[pivot][i] != residue<field>(b[i]-all)) return false;
    }
    if (std::none_of(first[0].begin(), first[0].end(), [](int x){return x != 0;})) return false;
    for (int i = 0; i < int(first[0].size()); ++i) {
        if ((first[0][i]+first[1][i]) % field) return false;
        for (int j = 2; j < y_dimension; ++j)
            if (first[j][i]) return false;
    }

    int generic = 0, old_pairs = 0;
    for (int g = 0; g < reserve_count; ++g) {
        if (g == pivot) continue;
        const auto where = std::find(positions.begin(), positions.end(), g);
        Matrix equations = transpose(features.projected[g]);
        for (int i = 0; i < int(equations.size()); ++i) equations[i].push_back(first[0][i]);
        const auto pivots = reduce<field>(equations);
        if (where == positions.end()) {
            if (pivots.size() != 34) return false;
            ++generic;
            continue;
        }
        if (pivots.size() != 33 || pivots.back() != 32) return false;
        constexpr auto inverse = inverses<field>();
        const Row& partner = old[where-positions.begin()];
        std::array<int, 2> hits{};
        for (int y0 = 0; y0 < field; ++y0) for (int y = 1; y < field; ++y) {
            const int scale = y0*(1-y0);
            if (residue<field>(y*(1-2*y0)+equations[0][33]*scale)) continue;
            if (residue<field>(y*y+equations[1][33]*scale)) continue;
            Row x(boolean_count);
            for (int i = 0; i < boolean_count; ++i)
                x[i] = residue<field>(y0-equations[2+i][33]*scale*inverse[y]);
            if (std::any_of(x.begin(), x.end(), [](int bit){return bit != 0 && bit != 1;})) continue;
            bool binary = true, difference = true, sum = true;
            for (int i = 0; i < selected; ++i) {
                const int a = residue<field>(inner<field>(features.top[i], x) +
                                    y0*features.images[pivot][i] + y*features.images[g][i]);
                binary &= a == 0 || a == residue<field>(b[i]);
                difference &= a == residue<field>((b[i]-partner[i])/2);
                sum &= a == residue<field>((b[i]+partner[i])/2);
                if (!binary) break;
            }
            if (!binary) continue;
            if ((!difference && !sum) || y0 != inverse[2]) return false;
            hits[sum]++;
        }
        if (hits != std::array<int,2>{1,1}) return false;
        ++old_pairs;
    }
    std::cout << "First reserve pivot: y-y^2; " << generic << " generic pairs and "
              << old_pairs << " pairs containing another old pivot, only existing lines\n";
    return generic == 581 && old_pairs == 14;
}

using Small = std::array<std::array<int,35>,40>;

std::array<int,2> small_rank(Small& a, int width) {
    constexpr auto inverse = inverses<field>();
    int rank = 0, last = -1;
    for (int j = 0; j < width; ++j) {
        int pivot = rank;
        while (pivot < int(a.size()) && a[pivot][j] == 0) ++pivot;
        if (pivot == int(a.size())) continue;
        auto& line = a[rank];
        std::swap(line, a[pivot]);
        const int scale = inverse[line[j]];
        for (int i = rank+1; i < int(a.size()); ++i) {
            if (!a[i][j]) continue;
            const int factor = field-a[i][j]*scale%field;
            for (int k = j+1; k < width; ++k) a[i][k] = (a[i][k]+factor*line[k]) % field;
        }
        ++rank;
        last = j;
    }
    return {rank,last};
}

bool check_coordinates(const Matrix& reduced_source, const Matrix& units, const Matrix& old, const Row& positions) {
    const auto features = axis_features(reduced_source, units, old[0]);
    if (features.projected.size() != reserve_count || !check_first_pivot(features, old, positions)) return false;
    const int first = positions[0];
    std::array<bool,reserve_count> is_old{};
    for (int pivot : positions) is_old[pivot] = true;
    int generic = 0, two_old = 0, anchored = 0;
    for (int j = 0; j < reserve_count; ++j) {
        if (j == first) continue;
        const Matrix kernel = kernel_rows<field>(features.projected[j]);
        if (kernel.size() != 40) return false;
        Matrix weighted = multiply<field>(kernel, features.left);
        Row pivot_vector(kernel.size());
        for (int i = 0; i < int(weighted.size()); ++i) {
            pivot_vector[i] = inner<field>(kernel[i], features.projected[first][0]);
            for (int n = 0; n < selected; ++n) weighted[i][n] = 2*weighted[i][n]*features.images[j][n] % field;
        }
        for (int k = j+1; k < reserve_count; ++k) {
            if (k == first) continue;
            const bool nonold = !is_old[j] && !is_old[k];
            Small image;
            for (int i = 0; i < int(image.size()); ++i) {
                for (int f = 0; f < y_dimension; ++f)
                    image[i][f] = inner<field>(kernel[i], features.projected[k][f]);
                image[i][33] = inner<field>(weighted[i], features.images[k]);
                image[i][34] = pivot_vector[i];
            }
            const auto [rank,last] = small_rank(image, nonold ? 35 : 34);
            if (is_old[j] && is_old[k]) {
                if (rank != 33 || last != 33) return false;
                ++two_old;
            } else {
                if (rank != (nonold ? 35 : 34)) return false;
                ++generic;
                anchored += nonold;
            }
        }
    }
    std::cout << "Reserve F13: " << generic << " rank-67 pairs, " << two_old
              << " rank-66 pairs with independent mixed term, " << anchored
              << " rank-68 triples with the first pivot\n";
    return generic == 176624 && two_old == 91 && anchored == 168490;
}

constexpr int signature_width = old_count+2;
using Signature = std::array<int,signature_width>;

std::array<Signature,selected> upper_cut_columns(const Matrix& a, const Matrix& b,
                                                const Matrix& units, const Row& signs) {
    std::array<Signature,selected> result{};
    auto row_maps = [](const Matrix& reduced){
        Matrix maps;
        for (const auto& row : reduced) maps.emplace_back(row.begin()+reserve_count, row.end());
        return transpose(maps);
    };
    const Matrix ra = row_maps(a), rb = row_maps(b);
    for (int i = 0; i < selected; ++i) {
        for (int j = 0; j < 2; ++j)
            result[i][j] = residue<d>(signs[i]*(92*ra[i][reserve_count+j]+208*rb[i][reserve_count+j]));
        for (int j = 0; j < old_count; ++j) {
            const int qa = residue<13>(-inner<13>(units[j],ra[i]));
            const int qb = residue<23>(-inner<23>(units[j],rb[i]));
            result[i][2+j] = residue<d>(signs[i]*(92*qa+208*qb));
        }
    }
    return result;
}

Signature plus(const Signature& a, const Signature& b) {
    Signature out;
    for (int c = 0; c < signature_width; ++c) out[c] = residue<d>(a[c]+b[c]);
    return out;
}

bool passes(const Signature& values, const Signature& alternate) {
    if (values[0] || values[1]) return false;
    for (int i = 2; i < signature_width; ++i)
        if (values[i] && values[i] != alternate[i]) return false;
    return true;
}

bool check_upper(const Matrix& p13, const Matrix& p23, const Matrix& units,
                 const Matrix& old, int first) {
    const auto columns = upper_cut_columns(p13,p23,units,old[0]);
    Signature epsilon{};
    for (int i = 0; i < old_count; ++i) epsilon[i+2] = residue<d>(units[i][first]-(i==0));
    if (std::accumulate(columns.begin(), columns.end(), Signature{}, plus) != epsilon) return false;
    std::array<std::uint64_t,6> scanned{}, survivors{};
    for (const Row& center : old) {
        auto flips = columns;
        Signature start{};
        for (int i = 0; i < selected; ++i) if (center[i] != old[0][i]) {
            start = plus(start,columns[i]);
            for (int& v : flips[i]) v = residue<d>(-v);
        }
        if (!passes(start,epsilon)) return false;
        Signature alternate{};
        for (int i = 2; i < signature_width; ++i) alternate[i] = residue<d>(epsilon[i]-2*start[i]);
        auto submit = [&](int size, const Signature& delta){
            ++scanned[size];
            survivors[size] += passes(delta,alternate);
        };
        for (const auto& row : flips) submit(1,row);
        std::vector<std::vector<std::array<int,3>>> buckets(d*d);
        for (int i = 0; i < selected; ++i) for (int j = i+1; j < selected; ++j) {
            auto two = plus(flips[i],flips[j]);
            submit(2,two);
            buckets[two[0]+d*two[1]].push_back({i,j,two[2]});
        }
        auto match = [&](int size, int before, const Signature& right){
            const int key = residue<d>(-right[0])+d*residue<d>(-right[1]);
            const int zero = residue<d>(-right[2]);
            const int changed = residue<d>(alternate[2]-right[2]);
            for (auto [a,b,moment] : buckets[key])
                if (b < before && (moment == zero || moment == changed))
                    submit(size,plus(right,plus(flips[a],flips[b])));
        };
        for (int i = 2; i < selected; ++i) match(3,i,flips[i]);
        for (int i = 2; i < selected; ++i) for (int j = i+1; j < selected; ++j) {
            const auto two = plus(flips[i],flips[j]);
            match(4,i,two);
            for (int k = j+1; k < selected; ++k) {
                const int key = residue<d>(-two[0]-flips[k][0])+d*residue<d>(-two[1]-flips[k][1]);
                const int zero = residue<d>(-two[2]-flips[k][2]);
                const int changed = residue<d>(zero+alternate[2]);
                for (auto [a,b,moment] : buckets[key])
                    if (b < i && (moment == zero || moment == changed))
                        submit(5,plus(plus(two,flips[k]),plus(flips[a],flips[b])));
            }
        }
    }
    std::cout << "Selected signs: radius 1-5 candidates";
    for (int i = 1; i <= 5; ++i) std::cout << ' ' << scanned[i];
    std::cout << "; after all CRT and moment cuts";
    for (int i = 1; i <= 5; ++i) std::cout << ' ' << survivors[i];
    std::cout << '\n';
    return scanned == std::array<std::uint64_t,6>{0,9000,2695500,21,6090,715147} &&
           survivors == std::array<std::uint64_t,6>{};
}

int main(int argc, char** argv) {
    if (argc != 2) return 1;
    const std::string_view section = argv[1];
    Row positions(old_count);
    Matrix units(units_count,Row(reserve_count)), old(old_count,Row(selected));
    Matrix source(height,Row(height));
    for (int& x : positions) std::cin >> x;
    for (auto* matrix : {&units,&old,&source})
        for (auto& row : *matrix) for (int& x : row) std::cin >> x;
    if (!std::cin || positions[0] != 136 ||
        std::any_of(positions.begin(),positions.end(),[](int i){return i < 0 || i >= reserve_count;})) return 2;
    const auto p13 = reserve_first<13>(source);
    if (p13.empty()) return 3;
    if (section != "selected" && !check_coordinates(p13,units,old,positions)) return 4;
    if (section != "reserve") {
        const auto p23 = reserve_first<23>(source);
        if (p23.empty() || !check_upper(p13,p23,units,old,positions[0])) return 5;
    }
}
