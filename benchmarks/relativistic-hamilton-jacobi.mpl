#
# Hamilton-Jacobi equation for a relativistic particle in flat space-time - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
restart;
with(sade):
v:=q1,q2,q3,tau:
eq:=diff(S(v),tau)^2-diff(S(v),q1)^2-diff(S(v),q2)^2-diff(S(v),q3)^2-1;
t1:=time():
gens:=liesymmetries(eq,[S(v)]);
time()-t1;
nops(gens[1]);
quit


