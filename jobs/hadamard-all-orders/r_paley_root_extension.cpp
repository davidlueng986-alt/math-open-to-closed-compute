#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using Matrix = std::vector<std::vector<int>>;

int mod(int x, int p) {
    int r=x%p;
    return r<0 ? r+p : r;
}

int inv(int x, int p) {
    for (int j=1;j<p;++j) if (x*j%p==1) return j;
    return 0;
}

std::vector<int> reduced(Matrix &a,int p) {
    for (auto &row:a) for (int &x:row) x=mod(x,p);
    std::vector<int> pivots;
    for (int j=0;j<int(a.front().size()) && pivots.size()<a.size();++j) {
        int k=pivots.size(),i=k;
        while(i<int(a.size()) && a[i][j]==0) ++i;
        if (i==int(a.size())) continue;
        std::swap(a[k],a[i]);
        int scale=inv(a[k][j],p);
        for (int s=j;s<int(a[k].size());++s) a[k][s]=a[k][s]*scale%p;
        for (int r=0;r<int(a.size());++r) if (r!=k && a[r][j]) {
            int c=a[r][j];
            for (int s=j;s<int(a[r].size());++s) a[r][s]=mod(a[r][s]-c*a[k][s],p);
        }
        pivots.push_back(j);
    }
    return pivots;
}

Matrix kernel(Matrix a, int p) {
    auto pivots=reduced(a,p);
    int n=a.front().size();
    std::vector<int> free;
    for (int j=0;j<n;++j) {
        if (!std::binary_search(pivots.begin(),pivots.end(),j)) free.push_back(j);
    }
    Matrix k(n,std::vector<int>(free.size(),0));
    for (int c=0;c<int(free.size());++c) {
        k[free[c]][c]=1;
        for (int i=0;i<int(pivots.size());++i) k[pivots[i]][c]=mod(-a[i][free[c]],p);
    }
    return k;
}

int main() {
    constexpr int m=1196, selected=600, units=15, n=selected+units;
    std::vector<int> signs(selected);
    for (int &x: signs) std::cin>>x;
    Matrix a(m,std::vector<int>(n));
    Matrix d(m,std::vector<int>(units));
    for (int i=0;i<m;++i) {
        for (int &x:a[i]) std::cin>>x;
        std::copy(a[i].begin()+selected,a[i].end(),d[i].begin());
    }
    if (!std::cin || !std::all_of(signs.begin(),signs.end(),[](int x){return x==1 || x==-1;}))
        return 1;
    if (reduced(d,23).size()!=units) return 2;
    Matrix basis=kernel(a,13);
    int dim=basis.front().size();
    if (dim!=17) return 3;
    Matrix transposed(dim,std::vector<int>(selected));
    for (int i=0;i<selected;++i) for (int j=0;j<dim;++j) transposed[j][i]=basis[i][j];
    auto choices=reduced(transposed,13);
    if (int(choices.size())!=dim) return 4;
    Matrix square(dim,std::vector<int>(2*dim,0));
    for (int i=0;i<dim;++i) {
        std::copy(basis[choices[i]].begin(),basis[choices[i]].end(),square[i].begin());
        square[i][dim+i]=1;
    }
    auto piv=reduced(square,13);
    if (int(piv.size())!=dim || piv.back()!=dim-1) return 5;
    Matrix c(selected,std::vector<int>(dim,0));
    for (int i=0;i<selected;++i) for (int j=0;j<dim;++j) {
        int s=0;
        for (int k=0;k<dim;++k) s+=basis[i][k]*square[k][dim+j];
        c[i][j]=mod(s*signs[choices[j]],13);
    }
    int count=0;
    for (uint32_t mask=0;mask<(uint32_t(1)<<dim);++mask) {
        bool valid=true;
        for (int i=0;i<selected;++i) {
            int s=0;
            for (uint32_t bits=mask;bits;bits&=bits-1) s+=c[i][std::countr_zero(bits)];
            s%=13;
            if (s!=0 && s!=mod(signs[i],13)) {
                valid=false;
                break;
            }
        }
        if (valid) {
            ++count;
            if (mask!=0) return 6;
        }
    }
    if (count!=1) return 7;
    std::cout<<"Fixed width1215: only zero among 131072 unit-supported sign assignments modulo 13, full unit-image rank modulo 23.\n";
}
