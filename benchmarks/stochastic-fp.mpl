#
# Stochastic Fokker-Planck equation - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
# In this case, the determining system is not fully solved and the routine returns a generic form
# for the generators, with functions satisfying a given set of differential equations,
# which must be analysed by the user to identify different cases and the corresponding algebra
# of admited generators (see reference above).
#
with(sade):
eq:=diff(u(x1,x2),x2)=A(x1)*u(x1,x2)+B(x1)*diff(u(x1,x2),x1)+C(x1)*diff(u(x1,x2),x1,x1);
t1:=time();
gens:=liesymmetries(eq,[u(x1,x2)],freefunctions={A(x1),B(x1),C(x1)});
time()-t1;
nops(gens[1]);
quit

