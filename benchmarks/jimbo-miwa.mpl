#
# Jimbo-MIwa equation - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
with(sade):
uu:=u(x1,x2,x3,x4):
eq:=2*diff(uu,x4,x2)-3*diff(uu,x1,x3)+3*diff(uu,x2)*diff(uu,x1,x1)+3*diff(uu,x1)*diff(uu,x1,x2)+diff(uu,x1$3,x2);
t1:=time():
gens:=liesymmetries(eq,[uu]);
time()-t1;
nops(gens[1]);
quit

