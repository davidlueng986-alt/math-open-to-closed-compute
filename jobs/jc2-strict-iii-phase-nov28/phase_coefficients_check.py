"""Exact characteristic-zero Lagrange coefficient check for same-P phases.
The input P is monic degree12 with P11=0. T has degree<=10.
No curve existence or analytic contact hypothesis is inferred by this script.
"""
from pathlib import Path
import sympy as s
z=s.symbols('z')
p10,p9,p8,p7=s.symbols('p10 p9 p8 p7')
cs={j:s.symbols(f'T{j}') for j in range(5,11)}
Pn=1+p10*z**2+p9*z**3+p8*z**4+p7*z**5
values={}
for j in [9,7,5]:
    series=s.series(Pn**(-s.Rational(j,12)),z,0,11-j).removeO()
    actual=s.expand(sum(s.Rational(k,j)*cs[k]*series.coeff(z,k-j) for k in range(j,11)))
    values[j]=actual
expected9=cs[9]
expected7=cs[7]-s.Rational(3,4)*cs[9]*p10-s.Rational(5,6)*cs[10]*p9
expected5=cs[5]-s.Rational(7,12)*cs[7]*p10-s.Rational(2,3)*cs[8]*p9-s.Rational(3,4)*cs[9]*p8+s.Rational(17,32)*cs[9]*p10**2-s.Rational(5,6)*cs[10]*p7+s.Rational(85,72)*cs[10]*p10*p9
for j,expected in [(9,expected9),(7,expected7),(5,expected5)]:
    assert s.expand(values[j]-expected)==0
reduced=s.expand(values[5].subs(cs[9],0).subs(cs[7],s.Rational(5,6)*cs[10]*p9))
assert reduced==s.expand(cs[5]-s.Rational(2,3)*cs[8]*p9-s.Rational(5,6)*cs[10]*p7+s.Rational(25,36)*cs[10]*p10*p9)
text='\n'.join(f'[X^{j}] T(t(X)) = {values[j]}' for j in [9,7,5])+'\nReduced fifth constraint = '+str(reduced)+'\n'
Path(__file__).with_name('phase_coefficients_exact.txt').write_text(text)
print(text)
print('All exact Laurent/Lagrange coefficient identities passed over QQ.')
