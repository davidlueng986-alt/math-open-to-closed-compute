#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <vector>

namespace {
constexpr int t = 11;
constexpr int size = 4*t;
using Word = std::array<int,t>;
using Mask = std::uint64_t;
using Lags = std::int64_t;
constexpr Mask word_mask = (1ULL << t)-1;
constexpr Mask graph_mask = (1ULL << size)-1;
constexpr std::array<Lags,5> lag_place{1,64,64*64,64*64*64,64*64*64*64};

// The first occupied sign can be fixed to +1 in each word. Store its exact
// (five nonredundant cyclic lags) and deduplicate by that lag vector.
std::array<std::vector<Lags>,1<<t> word_lags;

Mask rotate(Mask m,int d) {
    return ((m << d) | (m >> (t-d))) & word_mask;
}

void tabulate_word_lags() {
    for (Mask support = 0; support <= word_mask; ++support) {
        auto& lags = word_lags[support];
        if (!support) {
            lags.push_back(0);
            continue;
        }
        const Mask free_signs = support & (support-1);
        for (Mask minus = free_signs; ; minus = (minus-1)&free_signs) {
            const Mask plus = support ^ minus;
            Lags encoded=0;
            for (int d=1;d<=t/2;++d) {
                const Mask rp=rotate(plus,d), rm=rotate(minus,d);
                const int corr=std::popcount((rp&plus)|(rm&minus))-
                               std::popcount((rp&minus)|(rm&plus));
                encoded += corr*lag_place[d-1];
            }
            lags.push_back(encoded);
            if (!minus) break;
        }
        std::sort(lags.begin(),lags.end());
        lags.erase(std::unique(lags.begin(),lags.end()),lags.end());
    }
}


// Restrict location automorphisms to the exact affine group. The first-use
// relabeling makes each transformed support partition a unique word.
bool affine_canonical(const Word& word) {
    for (int a=0;a<t;++a) for (int b=1;b<t;++b) {
        std::array<int,4> rename{-1,-1,-1,-1};
        int next=0;
        for (int x=0;x<t;++x) {
            int& named=rename[word[(a+b*x)%t]];
            if (named<0) named=next++;
            if (named<word[x]) return false;
            if (named>word[x]) break;
        }
    }
    return true;
}

bool carries_t_signs(const std::array<Mask,4>& supports) {
    int odd=0;
    for (const Mask m:supports) odd += std::popcount(m)%2;
    if (odd!=3) return false; // zero mode at length 11 is (3,1,1,0) up to signs/order.
    std::array<const std::vector<Lags>*,4> bins;
    for (int j=0;j<4;++j) bins[j] = &word_lags[supports[j]];
    std::sort(bins.begin(),bins.end(),[](auto* u, auto* v){return u->size() < v->size();});
    const auto& [a,b,c,d]=bins;
    for (const Lags x:*a) for (const Lags y:*c) for (const Lags z:*b) {
        if (std::binary_search(d->begin(),d->end(),-x-y-z)) return true;
    }
    return false;
}

int mod_t(int x) { return (x%t+t)%t; }

std::array<std::array<Mask,size>,4> gs_columns(const Word& word) {
    std::array<std::array<Mask,size>,4> columns{};
    for (int row=0;row<size;++row) for (int col=0;col<size;++col) {
        const int a=row/t, b=col/t, x=row%t, y=col%t;
        int argument=0;
        if (a==b) argument=y-x;
        else if (a==0 || b==0) argument=-1-x-y;
        else argument=1+x+y;
        const int coefficient=(a^b)^word[mod_t(argument)];
        columns[coefficient][col] |= 1ULL<<row;
    }
    return columns;
}

int odd_triangle_vertices(const std::array<Mask,size>& a,
                          const std::array<Mask,size>& b,
                          const std::array<Mask,size>& c) {
    std::array<Mask,size> graph{};
    for (int i=0;i<size;++i) for (int j=0;j<size;++j) {
        if (std::popcount(a[i] & (b[j]|c[j]))%2) graph[i] |= 1ULL<<j;
    }
    for (int i=0;i<size;++i) {
        if ((graph[i]>>i)&1) return -1;
        for (int j=0;j<i;++j) if (((graph[i]>>j)^(graph[j]>>i))&1) return -1;
    }
    int bad=0;
    for (int i=0;i<size;++i) {
        int triangles=0;
        Mask neighbors=graph[i] & graph_mask;
        while (neighbors) {
            int j=std::countr_zero(neighbors);
            neighbors &= neighbors-1;
            triangles += std::popcount(neighbors & graph[j]);
        }
        bad += triangles%2;
    }
    return bad;
}

std::uint64_t partitions=0, affine_reps=0, signed_reps=0, mask_count=0;
std::map<int,int> histogram;

void visit(int length, int groups, Word& word, std::array<Mask,4>& supports) {
    if (length==t) {
        ++partitions;
        if (!affine_canonical(word)) return;
        ++affine_reps;
        if (!carries_t_signs(supports)) return;
        ++signed_reps;
        const auto columns=gs_columns(word);
        for (int a=0;a<4;++a) for (int unused=0;unused<4;++unused) {
            if (a==unused) continue;
            std::array<int,2> remainder;
            int k=0;
            for (int j=0;j<4;++j) if (j!=a && j!=unused) remainder[k++]=j;
            const auto [i,j]=remainder;
            const auto bad=odd_triangle_vertices(columns[a],columns[i],columns[j]);
            ++histogram[bad];
            ++mask_count;
            if (bad<=0) {
                std::cout << "surviving/malformed ternary support";
                for (const int v:word) std::cout << ' ' << v;
                std::cout << " designated=" << a << ',' << unused << " odd=" << bad << '\n';
            }
        }
        return;
    }
    for (int j=0;j<std::min(groups+1,4);++j) {
        word[length]=j;
        supports[j] |= 1ULL<<length;
        visit(length+1, std::max(groups,j+1), word,supports);
        supports[j] ^= 1ULL<<length;
    }
}
}

int main() {
    tabulate_word_lags();
    Word word{};
    std::array<Mask,4> supports{};
    visit(0,0,word,supports);
    std::cout << "T11 support census: partitions=" << partitions
              << " affine_reps=" << affine_reps << " signed_reps=" << signed_reps
              << " mask_count=" << mask_count << '\n';
    for (const auto [odd,count]:histogram) std::cout << "odd_vertices=" << odd << " masks=" << count << '\n';
    const std::map<int,int> expected{{8,16},{16,156},{24,248},{32,76},{40,8}};
    return partitions != 175275 || affine_reps != 1665 || signed_reps != 42 ||
           mask_count != 504 || histogram != expected;
}
