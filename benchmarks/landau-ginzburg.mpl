#
# 3-dimensional Landau-Ginzburg equation - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
# The symmetry generators are obtained in cases of the free parameter values.
#
with(sade):
uu:=u(x1,x2,x3,x4);
eq:=diff(uu,x1,x1)+diff(uu,x2,x2)+diff(uu,x3,x3)+diff(uu,x4)=a1+a2*uu+a3*uu^3+a4*uu^5;
t1:=time():
gens:=liesymmetries(eq,[u(x1,x2,x3,x4)],parameters={a1,a2,a3,a4});
time()-t1;
quit
