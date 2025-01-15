#
# Carleman-Boltzmann equation - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
with(sade):
eq:=diff(u(x1,x2),x1,x1)-diff(u(x1,x2),x2,x2)-2*diff(u(x1,x2),x1)*diff(u(x1,x2),x2);
t1:=time():
gens:=liesymmetries(eq,[u(x1,x2)]);
time()-t1;
nops(gens[1]);
quit
