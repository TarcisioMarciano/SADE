# Gross-Neveu equation
with(sade):
# Here we define the Dirac matrices
g0:=matrix([[1,0,0,0],[0,1,0,0],[0,0,-1,0],[0,0,0,-1]]);
g1:=matrix([[0,0,0,1],[0,0,1,0],[0,-1,0,0],[-1,0,0,0]]);
g2:=matrix([[0,0,0,-I],[0,0,I,0],[0,I,0,0],[-I,0,0,0]]);
g3:=matrix([[0,0,1,0],[0,0,0,-1],[-1,0,0,0],[0,1,0,0]]);
# We define the spinor as a vector with complex components, each with a real and imaginary part,
# which are taken here as the dependent variables
psi:=matrix([[phi1r(x1,x2,x3,t)+I*phi1i(x1,x2,x3,t)],[phi2r(x1,x2,x3,t)+I*phi2i(x1,x2,x3,t)],
             [phi3r(x1,x2,x3,t)+I*phi3i(x1,x2,x3,t)],[phi4r(x1,x2,x3,t)+I*phi4i(x1,x2,x3,t)]]);
# The conjugate spinor:
psi_b:=subs(I=-I,transpose(psi));
# Now we obtain the Gross-Neveu equations:
a1:=map(x->diff(x,x1),psi):
a2:=map(x->diff(x,x2),psi):
a3:=map(x->diff(x,x3),psi):
a0:=map(x->diff(x,t),psi):

b1:=evalm(evalm(psi_b.g0).psi);
b2:=expand(lambda_c*b1[1,1]);
eq:=evalm(I*(g0.a0+g1.a1+g2.a2+g3.a3)-evalm(m*psi)-evalm(b2*psi)):
eqs:=expand([eq[1,1],eq[2,1],eq[3,1],eq[4,1]]):
# Real and imaginary parts of the equations, respectivelly:
eqs_r:=subs(I=0,eqs):
eqs_i:=map(x->coeff(x,I),eqs):
# Computing Lie symmetries
SADE[traceout]:=true;
t1:=time():
s1:=liesymmetries({op(eqs_r),op(eqs_i)},
         [phi1r(x1,x2,x3,t),phi2r(x1,x2,x3,t),phi3r(x1,x2,x3,t),phi4r(x1,x2,x3,t),
          phi1i(x1,x2,x3,t),phi2i(x1,x2,x3,t),phi3i(x1,x2,x3,t),phi4i(x1,x2,x3,t)]):
time()-t1;
s1[2];
nops(s1[1]);
s2:=[op(s1[1])]:
# Displaying the generators
for i from 1 to nops(s2) do print(i,s2[i]) od:
# And finally computing the comutation table for the symmetry algebra:
com_table(s2,[phi1r,phi2r,phi3r,phi4r,phi1i,phi2i,phi3i,phi4i,x1,x2,x3,t],T);

