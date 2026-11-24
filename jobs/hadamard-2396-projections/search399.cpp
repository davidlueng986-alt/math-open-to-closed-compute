// Exhaust the 3-point refinements of one pair of invariant 133-point rows.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

using Word = std::uint64_t;
using Triple = std::array<int,3>;
using Shape = std::array<int,9>;
using Row = std::array<int,399>;
using Matrix = std::array<std::array<Word,27>,27>;
constexpr int available = 199; // Number of magnitude-three entries across both rows.
constexpr Shape weights{1,9,9,3,27,27,3,27,27};
constexpr Shape order{4,5,7,8,1,2,3,6,0};

int orbit(int n, int p) {
    if (n % p == 0) return 0;
    for (int x=1; x<p; ++x) if (x*x % p == n%p) return 1;
    return 2;
}

Word next_weight(Word& state) {
    state += 0x9e3779b97f4a7c15ULL;
    Word value = (state ^ (state >> 30)) * 0xbf58476d1ce4e5b9ULL;
    value = (value ^ (value >> 27)) * 0x94d049bb133111ebULL;
    return value ^ (value >> 31);
}

struct Checksum {
    Matrix terms{};
    std::array<Word,200> coeff{};
    Word target = 0;
    Checksum() {
        Word state = 2396;
        for (auto& x : coeff) x = next_weight(state);
        target = Word(2390)*coeff[0];
        for (int s=1; s<200; ++s) target -= Word(6)*coeff[s];
        Row index{};
        for (int t=0; t<399; ++t) index[t] = 3*(3*orbit(t,7)+orbit(t,19))+t%3;
        for (int i=0; i<399; ++i) for (int j=i; j<399; ++j) {
            const int d = std::min(j-i,399-(j-i));
            const int a = std::min(index[i],index[j]), b = std::max(index[i],index[j]);
            terms[a][b] += coeff[d];
        }
    }
    Word direct(const Row& row) const {
        Word key = 0;
        for (int s=0; s<200; ++s) {
            int value = 0;
            for (int i=0; i<399; ++i) value += row[i]*row[(i+s)%399];
            key += coeff[s]*Word(value);
        }
        return key;
    }
    Word combine(int i,const Triple& u,int j,const Triple& v) const {
        Word value=0;
        for (int a=0; a<3; ++a) for (int b=0; b<3; ++b) {
            if (i==j && a>b) continue;
            const int low=std::min(3*i+a,3*j+b), high=std::max(3*i+a,3*j+b);
            value += terms[low][high]*Word(u[a]*v[b]);
        }
        return value;
    }
};

struct Choice {Triple values, sums; int threes; Word own;};
using Counts = std::array<bool,available+1>;
using Options = std::array<std::vector<Choice>,9>;

struct Space {
    Options choices;
    std::array<Counts,10> suffix{}, allowed{};
    Word cross[9][12][9][12]{};
    std::uint64_t compatible_energy=0, compatible_dc=0;
    Shape selected{};
    explicit Space(const Shape& shape,const Checksum& checksum) {
        suffix[9][0] = true;
        for (int level=8; level>=0; --level) {
            int i=order[level];
            for (int x:{-3,-1,1,3}) for (int y:{-3,-1,1,3}) for (int z:{-3,-1,1,3}) {
                if (x+y+z != shape[i]) continue;
                Triple u{x,y,z}, sums{};
                for (int t=0; t<3; ++t) sums[t]=weights[i]*u[t];
                const int cost=weights[i]*((x*x==9)+(y*y==9)+(z*z==9));
                choices[level].push_back({u,sums,cost,checksum.combine(i,u,i,u)});
                for (int v=cost; v<=available; ++v)
                    if (suffix[level+1][v-cost]) suffix[level][v]=true;
            }
            if (choices[level].empty() || choices[level].size()>12) throw std::logic_error("bad slice");
        }
        for (int hi=0; hi<9; ++hi) for (int lo=0; lo<hi; ++lo)
            for (unsigned u=0; u<choices[hi].size(); ++u) for (unsigned v=0; v<choices[lo].size(); ++v)
                cross[hi][u][lo][v]=checksum.combine(order[hi],choices[hi][u].values,order[lo],choices[lo][v].values);
    }
    void restrict_to(const Space& other) {
        for (int level=0; level<=9; ++level) for (int used=0; used<=available; ++used)
            for (int extra=0; extra<=available-used; ++extra)
                if (suffix[level][extra] && other.suffix[0][available-used-extra]) {
                    allowed[level][used]=true;
                    break;
                }
    }
    template<typename Consumer>
    void enumerate(int level,int count,Triple sums,Word key,Word code,Consumer& consume) {
        if (count>available || !allowed[level][count]) return;
        if (level==9) {
            ++compatible_energy;
            if (sums[0]*sums[0]+sums[1]*sums[1]+sums[2]*sums[2]>1598) return;
            ++compatible_dc;
            consume(key,code);
            return;
        }
        for (unsigned opt=0; opt<choices[level].size(); ++opt) {
            const auto& value=choices[level][opt];
            const int next=count+value.threes;
            if (next>available || !allowed[level+1][next]) continue;
            Word offset=value.own;
            for (int j=0; j<level; ++j) offset+=cross[level][opt][j][selected[j]];
            Triple updated=sums;
            for (int k=0; k<3; ++k) updated[k]+=value.sums[k];
            selected[level]=opt;
            enumerate(level+1,next,updated,key+offset,code | (Word(opt)<<(4*level)),consume);
        }
    }
    Row materialize(Word code) const {
        std::array<Triple,9> values{};
        for (int i=0; i<9; ++i)
            values[order[i]]=choices[i].at((code>>(4*i)) & 15).values;
        Row result{};
        for (int i=0; i<399; ++i) result[i]=values[3*orbit(i,7)+orbit(i,19)][i%3];
        return result;
    }
};

bool is_projection(const Row& a,const Row& b) {
    for (int s=0; s<399; ++s) {
        int total=0;
        for (int i=0; i<399; ++i) total+=a[i]*a[(i+s)%399]+b[i]*b[(i+s)%399];
        if (total!=(s==0?2390:-6)) return false;
    }
    return true;
}

void print_row(const Row& a) {
    std::cout<<"[";
    for (int i=0; i<399; ++i) std::cout<<(i?",":"")<<a[i];
    std::cout<<"]";
}

int main() {
    Shape a{},b{};
    for (auto* row : {&a,&b}) for (auto& x : *row) if (!(std::cin>>x)) return 2;
    Checksum checksum;
    Space first(a,checksum),second(b,checksum);
    first.restrict_to(second);
    second.restrict_to(first);
    std::unordered_multimap<Word,Word> table; // Keep all collisions.
    Word control_code = 0, control_key = 0;
    bool have_control = false, passed_control = false;
    auto put=[&](Word key,Word code){
        if (!have_control) {
            control_key = checksum.direct(first.materialize(code));
            if (control_key!=key) throw std::logic_error("left scalar checksum mismatch");
            control_code=code;
            have_control=true;
        }
        table.emplace(key,code);
    };
    first.enumerate(0,0,{},0,0,put);
    Word hash_hits=0, actual=0;
    Row witness1{},witness2{};
    auto match=[&](Word key,Word code) {
        if (have_control && !passed_control) {
            Word known_target = control_key + checksum.direct(second.materialize(code));
            auto [lo,hi] = table.equal_range(known_target-key);
            for (; lo!=hi; ++lo) if (lo->second==control_code) passed_control=true;
            if (!passed_control) throw std::logic_error("failed known pair checksum join");
        }
        auto [it,end]=table.equal_range(checksum.target-key);
        for (; it!=end; ++it) {
            ++hash_hits;
            Row u=first.materialize(it->second),v=second.materialize(code);
            if (is_projection(u,v)) {
                if (actual++==0) {witness1=u; witness2=v;}
            }
        }
    };
    second.enumerate(0,0,{},0,0,match);
    if (!passed_control) throw std::logic_error("no control pair");
    std::cout<<"{\"positive_checksum_control\":true,\"rows_after_energy\":["<<first.compatible_energy<<","<<second.compatible_energy
             <<"],\"rows_after_dc\":["<<first.compatible_dc<<","<<second.compatible_dc
             <<"],\"hash_matches\":"<<hash_hits<<",\"solutions\":"<<actual<<",\"first_witness\":";
    if (actual) {std::cout<<"[";print_row(witness1);std::cout<<",";print_row(witness2);std::cout<<"]";}
    else std::cout<<"null";
    std::cout<<"}\n";
}
