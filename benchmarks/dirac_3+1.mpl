#
# Dirac equation - - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#

with(sade):

# Here we define the Dirac matrices
g0:=matrix([[1,0,0,0],[0,1,0,0],[0,0,-1,0],[0,0,0,-1]]);
g1:=matrix([[0,0,0,1],[0,0,1,0],[0,-1,0,0],[-1,0,0,0]]);
g2:=matrix([[0,0,0,-I],[0,0,I,0],[0,I,0,0],[-I,0,0,0]]);
g3:=matrix([[0,0,1,0],[0,0,0,-1],[-1,0,0,0],[0,1,0,0]]);

# We define the spinor as a vector with complex components, each with a real and imaginary part,
# which are taken here as the dependent variables
psi:=matrix([[u1(x1,x2,x3,t)+I*v1(x1,x2,x3,t)],[u2(x1,x2,x3,t)+I*v2(x1,x2,x3,t)],
             [u3(x1,x2,x3,t)+I*v3(x1,x2,x3,t)],[u4(x1,x2,x3,t)+I*v4(x1,x2,x3,t)]]);

# The conjugate spinor:
psi_b:=subs(I=-I,transpose(psi));



# Now we obtain the components of the Dirac spinorial equation

a1:=map(x->diff(x,x1),psi):
a2:=map(x->diff(x,x2),psi):
a3:=map(x->diff(x,x3),psi):
a0:=map(x->diff(x,t),psi):

eq:=evalm(I*(g0.a0+g1.a1+g2.a2+g3.a3)-evalm(m*psi)):
eqs:=expand([eq[1,1],eq[2,1],eq[3,1],eq[4,1]]):

# Real and imaginary parts of the equations, respectivelly:
eqs_r:=subs(I=0,eqs);
eqs_i:=map(x->coeff(x,I),eqs);



# Computing Lie symmetries
t1:=time():
s1:=liesymmetries({op(eqs_r),op(eqs_i)},
         [u1(x1,x2,x3,t),u2(x1,x2,x3,t),u3(x1,x2,x3,t),u4(x1,x2,x3,t),
          v1(x1,x2,x3,t),v2(x1,x2,x3,t),v3(x1,x2,x3,t),v4(x1,x2,x3,t)]):
time()-t1;

nops(s1[1]);


s2:=s1[1]:
# Displaying the generators
for i from 1 to nops(s2) do print(i,s2[i]) od:


# And finally computing the comutation table for the symmetry algebra:
ff:={seq(cat(_F,i),i=1..6)}:
s3:=s2:
for i from 1 to 6 do
    s3:=map(x->if has(x,cat(_F,i)) then 0 else x fi,s3) minus {0}
od:
nops(s3);

com_table(s3,[u1,u2,u3,u4,v1,v2,v3,v4,x1,x2,x3,t],T);

quit
