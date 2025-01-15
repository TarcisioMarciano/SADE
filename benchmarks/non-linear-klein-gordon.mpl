#
# Non-linear Klein-Gordon equation - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
# The symmetry generators are obtained considering all cases for the free parameter values a2, a4 and a6.
#
with(sade):
m:=4;
p:=psi(seq(cat(x,i),i=1..m));
eq:=diff(p,cat(x,m)$2):
for i from 1 to m-1 do
    eq:=eq-diff(p,cat(x,i)$2)
od:
eq:=eq=-2*(a2*p+2*a4*p^3+3*a6*p^5);
t1:=time():
gens:=liesymmetries(eq,[p],parameters={a2,a4,a6});
time()-t1;
nops(gens);
quit
