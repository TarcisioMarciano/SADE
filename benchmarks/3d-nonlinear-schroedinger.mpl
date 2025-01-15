#
# Non-linear SChoedinger equation - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
# This case is an example of the use of the options parameters to obtain cases for the symmetry
# algebra acording to free parameter values.
#
# Note that psi is a complex quantity, and must be treated accordingly. u1 and u2 are its real and complex components, respectivelly.
#
with(sade):
psi:=u1(x1,x2,x3,x4)+I*u2(x1,x2,x3,x4);
psic:=u1(x1,x2,x3,x4)-I*u2(x1,x2,x3,x4);
eq:=I*diff(psi,x4)+diff(psi,x1,x2)+diff(psi,x2,x2)+diff(psi,x3,x3)-(a0*psi+a1*psi*psic*psi+a2*(psi*psic)^2*psi);
eq:=expand(eq);
eqr:=coeff(eq,I,0);
eqi:=coeff(eq,I,1);
t1:=time():
gens:=liesymmetries({eqr,eqi},[u1(x1,x2,x3,x4),u2(x1,x2,x3,x4)],parameters={a0,a1,a2});
time()-t1;
quit
