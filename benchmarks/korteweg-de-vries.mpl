#
# Korteweg-de Vries equation - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
with(sade):
eq:=diff(u(x1,x2),x2)+u(x1,x2)*diff(u(x1,x2),x1)+diff(u(x1,x2),x1$3);
gens:=liesymmetries(eq,[u(x1,x2)]);
nops(gens[1]);
quit
