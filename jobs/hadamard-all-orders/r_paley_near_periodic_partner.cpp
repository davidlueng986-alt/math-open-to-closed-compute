#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

#if defined(__x86_64__) && defined(__GNUC__)
#include <immintrin.h>
#define PALEY_X86_LANES 1
#endif
using namespace std;
constexpr int Q=25;
using Row=array<int,Q>;
using Key=uint64_t;
vector<Row> halves(const vector<Row>& a,int first,int n){
    vector<Row> out(1<<n);
    for(int i=first;i<first+n;i++)
        for(int j=0;j<Q;j++)out[0][j]-=a[i][j];
    for(unsigned i=1;i<out.size();i++){
        int bit=__builtin_ctz(i);
        out[i]=out[i&(i-1)];
        for(int j=0;j<Q;j++)out[i][j]+=2*a[first+bit][j];
    }
    return out;
}
Key key_of(const Row& row,const vector<int>& pos,int sign){
    Key k=0;unsigned depth=0;
    for(int j:pos){
        int x=sign*row[j]+256;
        assert(x>=0&&x<512);
        k|=Key(x)<<(depth++*9);
    }
    return k;
}
int cost(int p){
    if(!p)return 0;
    return abs(p)==4?4:13;
}
void mixed(){
    int cases;
    cin>>cases;
    uint64_t matched=0;
    int lines=0;
    for(int run=0;run<cases;run++){
        int n;cin>>n;
        assert(n==25);
        Row odd{};
        for(int i=0;i<24;i++)cin>>odd[i];
        vector<Row> M(n);
        for(auto& row:M)for(int& x:row)cin>>x;
        auto left=halves(M,0,n/2);
        auto right=halves(M,n/2,n-n/2);
        vector<int> possible;
        int h=0;
        for(int j=0;j<24;j++){
            if(!odd[j])possible.push_back(j);
            else h+=abs(odd[j])>2;
        }
        assert(h<=2);
        int zero_bound = 24 - h - (37-13*h)/4;
        int available=possible.size();
        if(available<zero_bound)continue;
        int width=2;
        for(int k=3;k<=5;k++)if(available-available/k<zero_bound)width=k;
        assert(available-available/width<zero_bound);
        for(int start=0;start+width<=available;start+=width){
            vector<int> columns(possible.begin()+start,possible.begin()+start+width);
            vector<pair<Key,unsigned>> index;
            index.reserve(right.size());
            for(unsigned i=0;i<right.size();i++)index.emplace_back(key_of(right[i],columns,1),i);
            sort(index.begin(),index.end());
            for(unsigned l=0;l<left.size();l++){
                Key key=key_of(left[l],columns,-1);
                auto it=lower_bound(index.begin(),index.end(),pair{key,0U});
                for(;it!=index.end()&&it->first==key;it++){
                    ++matched;
                    const auto& r=right[it->second];
                    int c=cost(left[l][24]+r[24]);
                    bool parity=true;
                    for(int j=0; j<24 && c<=37; j++){
                        int p=left[l][j]+r[j]+2*odd[j];
                        int q=left[l][j]+r[j]-2*odd[j];
                        if(p%4||q%4){parity=false;break;}
                        c+=cost(p)+cost(q);
                    }
                    if(c<=37&&parity){++lines;cout<<"hit "<<run<<" "<<l<<" "<<it->second<<" "<<c<<"\n";}
                }
            }
        }
    }
    cout<<"matched "<<matched<<" records "<<lines<<"\n";
    assert(cin);
}


constexpr int pairs = 24;
using Phase = array<int,pairs>;

struct Symmetric {
    array<Phase,pairs> map{};
    Phase weights{}, given{}, partial{};
    uint64_t tested=0;

    void add(int j,int sign) {
        given[j]+=sign;
        for(int i=0;i<pairs;i++)partial[i]+=sign*map[j][i];
    }

    void test() {
        ++tested;
        int squared=0;
        for(int v:given)squared+=2*v*v;
        if(squared>6877)return;
        for(int j=0;j<pairs;j++){
            int v=(partial[j]%299+448)%299-149;
            if(abs(v)>69)return;
            squared+=weights[j]*v*v;
            if(squared>6877)return;
        }
        if(squared==6877){
            cout<<"hit";
            for(int v:given)cout<<" "<<v;
            cout<<"\n";
        }
    }

    void small(int left,int first) {
        if(!left){test();return;}
        for(int j=first;j<=pairs-left;j++)
            for(int sign:{-1,1}){
                add(j,sign);
                small(left-1,j+1);
                add(j,-sign);
            }
    }

    void scan() {
        for(int& w:weights)cin>>w;
        for(auto& row:map)for(int& x:row)cin>>x;
        for(int support=0;support<=4;support++)small(support,0);
        for(int large=0;large<pairs;large++)
            for(int value=2;value<=69;value++){
                add(large,value);
                test();
                for(int j=0;j<pairs;j++)if(j!=large)
                    for(int sign:{-1,1}){
                        add(j,sign);
                        test();
                        add(j,-sign);
                    }
                add(large,-value);
            }
        assert(tested==264065);
        cout<<"profiles "<<tested<<"\n";
    }
};


constexpr int physical = 1196;
constexpr int active = 49;
constexpr int payload_words = 16;
constexpr std::uint64_t lane_ones = 0x0001000100010001ULL;
constexpr std::uint64_t lane_high = 0x8000800080008000ULL;

struct alignas(64) Packed {
    std::array<std::uint64_t, payload_words> words{};

    void set(int index, unsigned value) {
        words[index / 4] |= std::uint64_t(value) << (16 * (index % 4));
    }
};

struct alignas(64) PairMasks {
    Packed positive, negative, different;
};

struct TripleInput {
    std::array<Packed, physical> rows{};
    std::array<int, physical> fibre{};
    Packed mask, lengths;

    void read() {
        for (int i = 0; i < active; ++i) {
            mask.set(i, 8191);
            lengths.set(i, 13);
        }
        for (int r = 0; r < physical; ++r) {
            std::cin >> fibre[r];
            for (int j = 0; j < active; ++j) {
                unsigned v;
                std::cin >> v;
                assert(v <= 8191);
                rows[r].set(j, v);
            }
        }
    }

    PairMasks pair(int r, int s, bool flip) const {
        PairMasks p;
        for (int i = 0; i < payload_words; ++i) {
            auto a = rows[r].words[i];
            auto b = rows[s].words[i] ^ (flip ? mask.words[i] : 0);
            p.positive.words[i] = a & b;
            p.negative.words[i] = (a | b) ^ mask.words[i];
            p.different.words[i] = a ^ b;
        }
        return p;
    }
};

std::uint64_t lane_count(std::uint64_t x) {
    x -= (x >> 1) & 0x5555555555555555ULL;
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (x + (x >> 8)) & 0x001f001f001f001fULL;
}

std::uint64_t lane_min(std::uint64_t x, std::uint64_t y) {
    const auto choose_y = ((((x | lane_high) - y) & lane_high) >> 15) * 0xffff;
    return (x & ~choose_y) | (y & choose_y);
}

template<bool flip>
int scalar_loss(const TripleInput& input, const PairMasks& p, const Packed& row, int cutoff) {
    int result = 0;
    for (int k = 0; k < (active + 3) / 4 && result <= cutoff; ++k) {
        auto c = row.words[k] ^ (flip ? input.mask.words[k] : 0);
        auto agreement = (p.positive.words[k] & c) |
                         (p.negative.words[k] & (c ^ input.mask.words[k]));
        auto majority = p.positive.words[k] | (p.different.words[k] & c);
        auto m = lane_count(majority);
        auto e = lane_min(lane_count(agreement), lane_min(m, input.lengths.words[k] - m));
        e += e >> 32;
        e += e >> 16;
        result += e & 0xffff;
    }
    return result;
}

#ifdef PALEY_X86_LANES

__attribute__((target("avx2")))
__m256i lane_count256(__m256i value) {
    const auto lut = _mm256_setr_epi8(0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,
                                      0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4);
    const auto mask = _mm256_set1_epi8(15);
    const auto lo = _mm256_and_si256(value, mask);
    const auto hi = _mm256_and_si256(_mm256_srli_epi16(value, 4), mask);
    const auto bytes = _mm256_add_epi8(_mm256_shuffle_epi8(lut, lo), _mm256_shuffle_epi8(lut, hi));
    return _mm256_maddubs_epi16(bytes, _mm256_set1_epi8(1));
}

template<bool flip>
__attribute__((target("avx2")))
int avx2_loss(const TripleInput& input, const PairMasks& p, const Packed& row, int cutoff) {
    int result = 0;
    for (int k = 0; k < payload_words && result <= cutoff; k += 4) {
        const auto m = _mm256_load_si256(reinterpret_cast<const __m256i*>(&input.mask.words[k]));
        const auto plus = _mm256_load_si256(reinterpret_cast<const __m256i*>(&p.positive.words[k]));
        const auto minus = _mm256_load_si256(reinterpret_cast<const __m256i*>(&p.negative.words[k]));
        const auto diff = _mm256_load_si256(reinterpret_cast<const __m256i*>(&p.different.words[k]));
        auto c = _mm256_load_si256(reinterpret_cast<const __m256i*>(&row.words[k]));
        if (flip) c = _mm256_xor_si256(c, m);
        auto both = _mm256_or_si256(_mm256_and_si256(plus, c),
                                     _mm256_and_si256(minus, _mm256_xor_si256(c, m)));
        auto maj = lane_count256(_mm256_or_si256(plus, _mm256_and_si256(diff, c)));
        auto length = _mm256_load_si256(reinterpret_cast<const __m256i*>(&input.lengths.words[k]));
        auto count = _mm256_min_epi16(lane_count256(both), _mm256_min_epi16(maj, _mm256_sub_epi16(length, maj)));
        auto sum = _mm256_madd_epi16(count, _mm256_set1_epi16(1));
        alignas(32) std::array<int, 8> lanes;
        _mm256_store_si256(reinterpret_cast<__m256i*>(lanes.data()), sum);
        for (int lane : lanes) result += lane;
    }
    return result;
}

template<bool flip>
__attribute__((target("avx512f,avx512bw,avx512bitalg")))
int avx512_loss(const TripleInput& input, const PairMasks& p, const Packed& row, int cutoff) {
    int result = 0;
    for (int k = 0; k < payload_words && result <= cutoff; k += 8) {
        const auto m = _mm512_load_si512(&input.mask.words[k]);
        const auto plus = _mm512_load_si512(&p.positive.words[k]);
        const auto minus = _mm512_load_si512(&p.negative.words[k]);
        const auto diff = _mm512_load_si512(&p.different.words[k]);
        auto c = _mm512_load_si512(&row.words[k]);
        if (flip) c = _mm512_xor_si512(c, m);
        auto both = _mm512_or_si512(_mm512_and_si512(plus, c),
                                     _mm512_and_si512(minus, _mm512_xor_si512(c, m)));
        auto maj = _mm512_popcnt_epi16(_mm512_or_si512(plus, _mm512_and_si512(diff, c)));
        auto length = _mm512_load_si512(&input.lengths.words[k]);
        auto count = _mm512_min_epi16(_mm512_popcnt_epi16(both),
                                       _mm512_min_epi16(maj, _mm512_sub_epi16(length, maj)));
        result += _mm512_reduce_add_epi32(_mm512_madd_epi16(count, _mm512_set1_epi16(1)));
    }
    return result;
}

#endif

int scalar_check(const TripleInput& input, const PairMasks& p, const Packed& row, bool flip) {
    int loss = 0;
    for (int k = 0; k < active; ++k) {
        auto bits = [k](const Packed& value) {
            return unsigned(value.words[k / 4] >> (16 * (k % 4))) & 8191;
        };
        auto c = bits(row) ^ (flip ? 8191 : 0);
        auto a = __builtin_popcount((bits(p.positive) & c) | (bits(p.negative) & (c ^ 8191)));
        auto b = __builtin_popcount(bits(p.positive) | (bits(p.different) & c));
        loss += std::min(a, std::min(b, 13 - b));
    }
    return loss;
}

void triples(int backend) {
    TripleInput input;
    input.read();
    using Loss = int (*)(const TripleInput&, const PairMasks&, const Packed&, int);
    Loss loss[2] = {scalar_loss<false>, scalar_loss<true>};
#ifdef PALEY_X86_LANES
    if (backend > 0 && __builtin_cpu_supports("avx2")) {
        loss[0] = avx2_loss<false>;
        loss[1] = avx2_loss<true>;
    }
    if (backend > 1 && __builtin_cpu_supports("avx512f") &&
        __builtin_cpu_supports("avx512bw") && __builtin_cpu_supports("avx512bitalg")) {
        loss[0] = avx512_loss<false>;
        loss[1] = avx512_loss<true>;
    }
#else
    (void)backend;
#endif

    // Validate the selected implementation against an uncompressed calculation.
    for (int r = 0; r < 32; ++r) {
        for (int s = r + 1; s < physical; s += 67) {
            for (int phase : {0, 1}) {
                auto pair = input.pair(r, s, phase);
                for (int t = s + 1; t < physical; t += 59)
                    for (int orientation : {0, 1})
                        assert(loss[orientation](input, pair, input.rows[t], 637) ==
                               scalar_check(input, pair, input.rows[t], orientation));
            }
        }
    }

    int best = 637;
    std::uint64_t tested = 0, ties = 0;
    std::array<int, 5> witness{};
    for (int r = 0; r < physical - 2; ++r) {
        for (int s = r + 1; s < physical - 1; ++s) {
            int last = input.fibre[r] == input.fibre[s] ? 0 : 1;
            for (int phase = 0; phase <= last; ++phase) {
                auto pair = input.pair(r, s, phase);
                for (int t = s + 1; t < physical; ++t) {
                    if (input.fibre[s] != input.fibre[t] || phase == 0) {
                        ++tested;
                        int v = loss[0](input, pair, input.rows[t], best);
                        if (v < best) {
                            best = v; ties = 0; witness = {r, s, t, phase, 0};
                        }
                        if (v == best) ++ties;
                    }
                    if (input.fibre[r] != input.fibre[t] &&
                        (input.fibre[s] != input.fibre[t] || phase == 1)) {
                        ++tested;
                        int v = loss[1](input, pair, input.rows[t], best);
                        if (v < best) {
                            best = v; ties = 0; witness = {r, s, t, phase, 1};
                        }
                        if (v == best) ++ties;
                    }
                }
            }
        }
    }
    assert(tested == 1120601768 && best == 63 && ties == 6);
    assert((witness == std::array<int, 5>{357, 422, 1007, 1, 1}));
    auto p = input.pair(witness[0], witness[1], witness[3]);
    assert(scalar_check(input, p, input.rows[witness[2]], witness[4]) == best);
    std::cout << "triples " << tested << " minimum " << best << " ties " << ties << "\n";
}

int main(int argc,char** argv) {
    assert(argc==2);
    string mode=argv[1];
    if(mode=="symmetric")Symmetric{}.scan();
    else if(mode=="triples")triples(2);
    else if(mode=="triples-avx2")triples(1);
    else if(mode=="triples-portable")triples(0);
    else{
        assert(mode=="mixed");
        mixed();
    }
    assert(cin);
}
