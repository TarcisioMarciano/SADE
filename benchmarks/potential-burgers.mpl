#
# Potential Burgers equation - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
with(sade):
eq:={diff(u(x1,x2),x2)-diff(u(x1,x2),x1,x1)-diff(u(x1,x2),x1)^2};
t1:=time():
s1:=liesymmetries(eq,[u(x1,x2)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit

