"""Exact phase coefficients for the strict-IV cubic phase orbit."""
from pathlib import Path
import sympy as s
z=s.symbols('z');p16,p15,p14,p13=s.symbols('p16 p15 p14 p13')
cs={j:s.symbols(f'T{j}') for j in range(10,16)}
Pn=1+p16*z*z+p15*z**3+p14*z**4+p13*z**5
actual={}
for j in [14,13,11,10]:
 series=s.series(Pn**(-s.Rational(j,18)),z,0,16-j).removeO()
 actual[j]=s.expand(sum(s.Rational(k,j)*cs[k]*series.coeff(z,k-j) for k in range(j,16)))
expected={
14:cs[14],
13:cs[13]-s.Rational(5,6)*cs[15]*p16,
11:cs[11]-s.Rational(13,18)*cs[13]*p16-s.Rational(7,9)*cs[14]*p15-s.Rational(5,6)*cs[15]*p14+s.Rational(145,216)*cs[15]*p16**2,
10:cs[10]-s.Rational(2,3)*cs[12]*p16-s.Rational(13,18)*cs[13]*p15-s.Rational(7,9)*cs[14]*p14+s.Rational(49,81)*cs[14]*p16**2-s.Rational(5,6)*cs[15]*p13+s.Rational(35,27)*cs[15]*p16*p15,
}
for j in expected:assert s.expand(actual[j]-expected[j])==0
red11=s.expand(actual[11].subs(cs[14],0).subs(cs[13],s.Rational(5,6)*cs[15]*p16))
red10=s.expand(actual[10].subs(cs[14],0).subs(cs[13],s.Rational(5,6)*cs[15]*p16))
assert red11==s.expand(cs[11]-s.Rational(5,6)*cs[15]*p14+s.Rational(5,72)*cs[15]*p16**2)
assert red10==s.expand(cs[10]-s.Rational(2,3)*cs[12]*p16-s.Rational(5,6)*cs[15]*p13+s.Rational(25,36)*cs[15]*p16*p15)
text='\n'.join(f'[X^{j}]T(t(X)) = {actual[j]}' for j in actual)+'\n'
text+='Reduced C11 = '+str(red11)+'\nReduced C10 = '+str(red10)+'\n'
Path(__file__).with_name('phase_IV_coefficients_exact.txt').write_text(text)
print(text);print('All exact QQ coefficient identities passed.')
