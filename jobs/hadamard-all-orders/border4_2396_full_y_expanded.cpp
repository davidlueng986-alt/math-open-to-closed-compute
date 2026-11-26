#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

namespace {
constexpr int n = 299, p = 13, width = 8192, half = 149;
using U = std::uint64_t;
using Mask = std::array<U, 3>;
using Bits = std::bitset<n>;

struct Site { Mask pos{}, neg{}; };
struct Response { unsigned code = 0; Mask flip{}; };

void add(Response& a, const Response& b) {
    a.code ^= b.code;
    for (int i = 0; i < 3; ++i) a.flip[i] ^= b.flip[i];
}

void read(Response& r) {
    std::cin >> r.code;
    for (auto& b : r.flip) std::cin >> b;
}

constexpr int raw_site(int x, int y) { return (92*x + 208*y) % n; }

Bits rotate(const Bits& a, int k) {
    return (a << k) | (a >> (n - k));
}

int norm(const Bits& plus, const Bits& minus, int d) {
    const auto u = rotate(plus, d), v = rotate(minus, d);
    return int((plus&u).count() + (minus&v).count())
         - int((plus&v).count() + (minus&u).count());
}

int margin_change(const Mask& x, const Site& q) {
    int value = 0;
    for (int k = 0; k < 3; ++k)
        value += std::popcount(x[k]&q.neg[k]) - std::popcount(x[k]&q.pos[k]);
    return 2*value;
}

struct Engine {
    std::array<int, 4> y{};
    std::array<unsigned, width> transform{};
    std::array<Response, half> unit{};
    std::array<std::array<int, n>, 2> top{};
    std::array<std::array<Site, 14>, 2> sites{};
    std::array<std::array<int, p>, 2> base{};
    Response origin{};
    std::array<std::vector<Response>, 4> options;

    void read_input() {
        for (int& x : y) std::cin >> x;
        for (auto& x : transform) std::cin >> x;
        read(origin);
        for (Response& r : unit) read(r);
        for (auto& row : top) for (int& x : row) std::cin >> x;
        for (int i = 0; i < 2; ++i) {
            for (int& z : base[i]) std::cin >> z;
            for (auto& s : sites[i]) {
                for (auto& v : s.pos) std::cin >> v;
                for (auto& v : s.neg) std::cin >> v;
            }
        }
        if (!std::cin) throw std::runtime_error("invalid source");
    }

    void init(int row) {
        Bits pos, neg;
        for (int i = 0; i < n; ++i) {
            if (top[row][i] > 0) pos.set(i);
            if (top[row][i] < 0) neg.set(i);
        }
        std::array<int, half> old{};
        for (int d = 1; d <= half; ++d) old[d-1] = norm(pos, neg, d);
        for (int k = 0; k < 4; ++k) {
            options[k].assign(width, {});
            int a = y[k], b = (23-a) % 23;
            for (unsigned z = 0; z < width; ++z) {
                unsigned u = transform[z];
                Bits flips;
                for (int x = 0; x < p; ++x) {
                    if (z >> x & 1) flips.set(raw_site(x, a));
                    if (u >> x & 1) flips.set(raw_site(x, b));
                }
                auto pp = pos^flips, mm = neg^flips;
                for (int d = 1; d <= half; ++d) {
                    int v = norm(pp, mm, d) - old[d-1];
                    if (v % 4) throw std::runtime_error("pair effect did not preserve mod four");
                    if ((v/4) & 1) add(options[k][z], unit[d-1]);
                }
            }
        }
    }
};
} // namespace

namespace {
struct Mode { unsigned mask=0; int sum=0; Response raw; };
struct Catalog {
    std::vector<Mode> values;
    std::array<std::vector<Mode>,53> sums;
    std::unordered_map<U,std::vector<Mode>> table;
};
U key(int sum,unsigned code){return (U(sum+26)<<23)|code;}

struct IndependentBlocks {
    Engine& engine;
    std::array<Catalog,8> blocks;
    std::array<long long,4> eligible{}, projected{}, balanced{}, exact{};
    std::array<std::array<int,p>,2> top_norm{};
    int best=1<<30;
    const char* out;

    IndependentBlocks(Engine& e,const char* path):engine(e),out(path){
        for(int r=0;r<2;++r){
            engine.init(r);
            for(int i=0;i<n;++i)top_norm[r][i%p]+=engine.top[r][i];
            for(int a=0;a<4;++a) {
                int phase=engine.y[a], adjoint=(23-phase)%23;
                Catalog& c=blocks[4*r+a];
                c.values.reserve(width-1);
                for(unsigned i=1;i<width;++i) {
                    unsigned reversed=engine.transform[i];
                    int amount=0;
                    for(int x=0;x<p;++x){
                        if(i>>x&1)amount+=engine.top[r][raw_site(x,phase)];
                        if(reversed>>x&1)amount+=engine.top[r][raw_site(x,adjoint)];
                    }
                    Mode rec{i,amount,engine.options[a][i]};
                    c.values.push_back(rec);
                    c.sums[amount+26].push_back(rec);
                    c.table[key(amount,rec.raw.code)].push_back(rec);
                }
            }
        }
    }

    void test(int k,const std::array<int,3>& label,const std::array<Mode,3>& choices) {
        ++projected[k];
        Response other=engine.origin;
        for(int i=0;i<k;++i)add(other,choices[i].raw);
        if(other.code)throw std::runtime_error("incorrect raw projection");
        if(margin_change(other.flip,engine.sites[0][0])||margin_change(other.flip,engine.sites[1][0]))return;
        ++balanced[k];
        auto top=top_norm;
        for(int i=0;i<k;++i) {
             int r=label[i]/4, y=engine.y[label[i]%4], z=(23-y)%23;
             unsigned f=choices[i].mask, g=engine.transform[f];
             for(int x=0;x<13;++x) {
                 if(f>>x&1)top[r][x]-=2*engine.top[r][raw_site(x,y)];
                 if(g>>x&1)top[r][x]-=2*engine.top[r][raw_site(x,z)];
             }
        }
        auto tail=engine.base;
        for(int r=0;r<2;++r)
            for(int j=0;j<13;++j)tail[r][j]+=margin_change(other.flip,engine.sites[r][j+1]);
        int E=0;
        for(int d=0;d<=6;++d){
            int v=(d==0?-553:46);
            for(int r=0;r<2;++r)
                for(int x=0;x<13;++x)
                    v+=top[r][x]*top[r][(x+d)%13]+2*tail[r][x]*tail[r][(x+d)%13];
            E+=(d?2:1)*v*v;
        }
        if(!E)++exact[k];
        if(E>=best)return;
        best=E;
        std::ofstream f(out);
        f<<E<<" "<<k;
        for(int i=0;i<k;++i)f<<" "<<label[i]<<" "<<choices[i].mask;
        for(U x:other.flip)f<<" "<<x;
        f<<"\n";
        std::cout<<"record "<<E<<" blocks "<<k<<std::endl;
    }

    void short_search(int max){
        const auto target=engine.origin.code;
        eligible[0]=1;
        if(!target)test(0,{},{});
        for(int a=0;a<8;++a){
            eligible[1]+=blocks[a].sums[26].size();
            auto hit=blocks[a].table.find(key(0,target));
            if(hit!=blocks[a].table.end())
                for(auto& u:hit->second)test(1,{a,0,0},{u,{},{}});
        }
        if(max<2)return;
        for(int a=0;a<8;++a)for(int b=a+1;b<8;++b){
            bool same=(a/4==b/4);
            for(const Mode& u:blocks[a].values) {
                if(!same&&u.sum)continue;
                int s=same?-u.sum:0;
                eligible[2]+=blocks[b].sums[s+26].size();
                auto hit=blocks[b].table.find(key(s,target^u.raw.code));
                if(hit!=blocks[b].table.end())
                    for(const Mode& v:hit->second)test(2,{a,b,0},{u,v,{}});
            }
        }
        if(max<3)return;
        for(int i=0;i<8;++i)for(int j=i+1;j<8;++j)for(int k=j+1;k<8;++k){
            int a=i,b=j,c=k;
            bool same=(i/4==k/4);
            if(!same&&j/4==k/4){a=j;b=k;c=i;}
            auto branch=[&](const Mode& u,const Mode& v){
                int needed=same?-u.sum-v.sum:0;
                if(needed<-26||needed>26)return;
                eligible[3]+=blocks[c].sums[needed+26].size();
                auto it=blocks[c].table.find(key(needed,target^u.raw.code^v.raw.code));
                if(it!=blocks[c].table.end())for(const Mode&w:it->second)test(3,{a,b,c},{u,v,w});
            };
            for(const Mode& u:blocks[a].values) {
                if(same){
                    for(const Mode& v:blocks[b].values)branch(u,v);
                }else{
                    for(const Mode& v:blocks[b].sums[-u.sum+26])branch(u,v);
                }
            }
        }
    }
};
}

namespace {
constexpr unsigned allowed_zero=6464;
struct Word {Bits pos,neg;};
Bits raw_mask(unsigned x,int y){
    Bits f;
    while(x){
        int j=std::countr_zero(x);x&=x-1;
        f.set(raw_site(j,y));
    }
    return f;
}
std::array<Bits,2> base_center(unsigned a,unsigned b,unsigned k){
    return {raw_mask(a,0)|raw_mask(k,13),
            raw_mask(b,0)|raw_mask(k,20)|raw_mask(k,14)|raw_mask(k,13)};
}
Word apply_flips(const Word& w,const Bits& b){return {w.pos^b,w.neg^b};}
int sum(const Word& w){return int(w.pos.count())-int(w.neg.count());}

struct CenterAndBlock {
    Engine& e;
    std::array<Word,2> seed;
    std::array<std::array<Bits,half>,2> edges;
    std::array<int,half> anchor_norm{};
    std::array<std::array<Response,width>,8> options{};
    std::array<std::array<std::array<Response,13>,8>,14> pol{};
    std::array<long long,2> signed_top{}, matched{}, balanced{}, exact{};
    int best=1<<30;
    const char* path;

    CenterAndBlock(Engine& engine,const char* out):e(engine),path(out){
        for(int r=0;r<2;++r){
            e.init(r);
            for(int i=0;i<n;++i){
                if(e.top[r][i]>0)seed[r].pos.set(i);
                if(e.top[r][i]<0)seed[r].neg.set(i);
            }
            for(int j=0;j<4;++j)
                for(unsigned f=0;f<width;++f)
                    options[4*r+j][f]=e.options[j][f];
            const auto P=seed[r].pos|seed[r].neg;
            for(int d=1;d<=half;++d){
                edges[r][d-1]=P&rotate(P,d);
                anchor_norm[d-1]+=norm(seed[r].pos,seed[r].neg,d);
            }
        }
        for(int g=0;g<14;++g){
            unsigned a=g==0?allowed_zero:0,b=g==0?0:(1U<<(g-1));
            auto center=base_center(a,b,b^e.transform[b]);
            for(int block=0;block<8;++block){
                int r=block/4,y=e.y[block%4];
                for(int j=0;j<13;++j){
                    auto q=raw_mask(1U<<j,y)|raw_mask(e.transform[1U<<j],(23-y)%23);
                    Response out;
                    for(int d=1;d<=half;++d){
                        auto same=(q^rotate(q,d))&(center[r]^rotate(center[r],d))&edges[r][d-1];
                        if(same.count()%2)add(out,e.unit[d-1]);
                    }
                    pol[g][block][j]=out;
                }
            }
        }
    }

    void score(const Response& v,const std::array<Word,2>& top,unsigned a,unsigned b,int block,unsigned f){
        const int changed=(block>=0);
        if(v.code)throw std::runtime_error("incorrect center projection");
        ++matched[changed];
        if(margin_change(v.flip,e.sites[0][0])||margin_change(v.flip,e.sites[1][0]))return;
        ++balanced[changed];
        auto w=e.base;
        std::array<std::array<int,p>,2> front{};
        for(int r=0;r<2;++r){
            for(int x=0;x<13;++x)w[r][x]+=margin_change(v.flip,e.sites[r][x+1]);
            for(int i=0;i<n;++i){
                int a=top[r].pos[i]-top[r].neg[i];
                front[r][i%13]+=a;
            }
        }
        int error=0;
        for(int d=0;d<=6;++d){
            int z=(d?-46:553);
            for(int r=0;r<2;++r)for(int i=0;i<p;++i)
                z-=2*w[r][i]*w[r][(i+d)%p]+front[r][i]*front[r][(i+d)%p];
            error+=(d?2:1)*z*z;
        }
        if(!error)++exact[changed];
        if(error>=best)return;
        best=error;
        std::ofstream out(path);
        out<<error<<" "<<a<<" "<<b<<" "<<block<<" "<<f;
        for(auto i:v.flip)out<<" "<<i;
        out<<"\n";
        std::cout<<"record "<<error<<" center and pair "<<block<<std::endl;
    }

    void run(){
        std::vector<Response> delta(width);
        for(unsigned a:{0U,allowed_zero})for(unsigned b=0;b<width;++b){
            if(std::popcount(b)%2)continue;
            auto center=base_center(a,b,b^e.transform[b]);
            auto q=std::array<Word,2>{apply_flips(seed[0],center[0]),apply_flips(seed[1],center[1])};
            std::array<int,2> s{sum(q[0]),sum(q[1])-1};
            if(s[0]&&s[1])continue;
            if((s[0]%2)||(s[1]%2))throw std::runtime_error("center violated sum parity");
            Response origin=e.origin;
            for(int d=1;d<=half;++d){
                int dd=norm(q[0].pos,q[0].neg,d)+norm(q[1].pos,q[1].neg,d)-anchor_norm[d-1];
                if(dd%4)throw std::runtime_error("center violated mod four");
                if((dd/4)&1)add(origin,e.unit[d-1]);
            }
            if(!s[0]&&!s[1]){
                ++signed_top[0];
                if(!origin.code)score(origin,q,a,b,-1,0);
            }
            unsigned center_choice=(b<<1)|(a?1U:0U);
            for(int block=0;block<8;++block){
                int r=block/4;
                if(s[1-r])continue;
                int y=e.y[block%4],z=(23-y)%23;
                unsigned pp=0,pm=0,mp=0,mm=0;
                for(int i=0;i<13;++i){
                    if(q[r].pos[raw_site(i,y)])pp|=1<<i;
                    if(q[r].neg[raw_site(i,y)])pm|=1<<i;
                    if(q[r].pos[raw_site(i,z)])mp|=1<<i;
                    if(q[r].neg[raw_site(i,z)])mm|=1<<i;
                }
                std::array<Response,13> polar;
                for(int j=0;j<13;++j){
                    auto z=center_choice;
                    while(z){
                        int k=std::countr_zero(z);
                        z&=z-1;
                        add(polar[j],pol[k][block][j]);
                    }
                }
                for(unsigned f=1;f<width;++f){
                    delta[f]=delta[f&(f-1)];
                    add(delta[f],polar[std::countr_zero(f)]);
                    unsigned a0=e.transform[f];
                    int g=std::popcount(f&pp)-std::popcount(f&pm)
                         +std::popcount(a0&mp)-std::popcount(a0&mm);
                    if(2*g!=s[r])continue;
                    ++signed_top[1];
                    const auto& v=options[block][f];
                    if((origin.code^v.code^delta[f].code))continue;
                    Response total=origin;
                    add(total,v);add(total,delta[f]);
                    auto words=q;
                    words[r]=apply_flips(words[r],raw_mask(f,y)|raw_mask(a0,z));
                    score(total,words,a,b,block,f);
                }
            }
        }
    }
};
}


int main(int argc, char** argv) {
    try {
        if (argc != 3) return 1;
        Engine e;
        e.read_input();
        const std::string mode = argv[1];
        if (mode == "independent") {
            IndependentBlocks s(e, argv[2]);
            s.short_search(3);
            for (int k = 0; k < 4; ++k)
                std::cout << k << " " << s.eligible[k] << " " << s.projected[k]
                          << " " << s.balanced[k] << " " << s.exact[k] << '\n';
        } else if (mode == "center") {
            CenterAndBlock s(e, argv[2]);
            s.run();
            for (int k = 0; k < 2; ++k)
                std::cout << k << " " << s.signed_top[k] << " " << s.matched[k]
                          << " " << s.balanced[k] << " " << s.exact[k] << '\n';
        } else {
            return 1;
        }
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
