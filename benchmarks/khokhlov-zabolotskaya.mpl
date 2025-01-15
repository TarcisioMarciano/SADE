#
# Khokhlov-Zabolotskaya equation in 2+1 dimensions - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
with(sade):
uu:=u(x1,x2,x3);
eq:=diff(uu,x1,x3)-diff(uu*diff(uu,x1),x1)=diff(uu,x2,x2);
t1:=time();
gens:=liesymmetries(eq,[u(x1,x2,x3)]);
time()-t1;
nops(gens[1]);
quit

