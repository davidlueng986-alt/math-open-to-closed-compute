import sympy as s
a,b,h,k,u,v,A,B=s.symbols("a b h k u v alpha beta")
F=lambda x:k+b*x*h-a*x*x
G=lambda x:v+b*x*u
R=b*b*u*u*k-b*b*h*u*v-a*v*v
assert s.expand(R-b*b*u*u*F(A)-G(A)*((2*a*b*A-b*b*h)*u-a*G(A)))==0
assert s.expand((A-B)**2*(R+a*G(A)*G(B))+(G(A)-G(B))*(F(A)*G(B)-F(B)*G(A)))==0
d,w,V=s.symbols("d w V")
p=w*(2-(d+1)*V)/(d-1);q=w*w*(1-d*V)/(d-1)
assert s.cancel(p*p-4*(d+1)/d**2*q-(w*(d*(d+1)*V-2)/(d*(d-1)))**2)==0
H1=d*w/(d+1);H2=d*w*(1-d*V)/(d-1)
assert s.cancel(q-h*p+(d+1)/d**2*h*h-(d+1)/d**2*(h-H1)*(h-H2))==0
r,p1,p2,p3,z=s.symbols("r p1 p2 p3 z",nonzero=True)
P=r*r+p1*z+p2*z*z+p3*z**3
sqrtP=r*s.series((P/r**2)**s.Rational(1,2),z,0,4).removeO()
c=s.expand(sqrtP).coeff(z,3)
assert s.cancel(c-(p3/(2*r)-p1*p2/(4*r**3)+p1**3/(16*r**5)))==0
assert s.cancel(3*c.subs({r:3**8*r,p1:3**13*p1,p2:3**10*p2,p3:3**7*p3}, simultaneous=True)-c)==0
v5=r**3*s.series((P/r**2)**s.Rational(3,2),z,0,5).removeO()
assert s.cancel(s.expand(v5).coeff(z,4)-3*p1*p3/(4*r)-3*(4*r*r*p2-p1*p1)**2/(128*r**5))==0
cp,cq,f5,g8,sigma,T=s.symbols("cp cq f5 g8 sigma T",nonzero=True)
expr=-(-cp*cq/3)*(cq*g8/T**3)*3*T*sigma-cq*cq*g8/f5*sigma
assert s.cancel(expr.subs(cp,T*T/f5))==0
print("ALL_EXACT_RING_AND_RESIDUE_IDENTITIES_PASS")
