#
# Maxwell-Dirac equations - W.-H. Steeb, Continuous Symmetries, Lie Algebras, Differential
# Equations and Computer Algebra, 2nd Ed, World Scientific (New Jersey, 2007).
#
with(sade):
# Here we define the Dirac matrices
g0:=matrix([[1,0,0,0],[0,1,0,0],[0,0,-1,0],[0,0,0,-1]]);
g1:=matrix([[0,0,0,1],[0,0,1,0],[0,-1,0,0],[-1,0,0,0]]);
g2:=matrix([[0,0,0,-I],[0,0,I,0],[0,I,0,0],[-I,0,0,0]]);
g3:=matrix([[0,0,1,0],[0,0,0,-1],[-1,0,0,0],[0,1,0,0]]);
vv:=x0,x1,x2,x3;
# We define the spinor as a vector with complex components, each with a real and imaginary part,
# which are taken here as the dependent variables
psi:=matrix([[u1(vv)+I*v1(vv)],[u2(vv)+I*v2(vv)],
             [u3(vv)+I*v3(vv)],[u4(vv)+I*v4(vv)]]);
# The conjugate spinor:
psi_b:=matrix([[u1(vv)-I*v1(vv),u2(vv)-I*v2(vv),
             -u3(vv)+I*v3(vv),-u4(vv)+I*v4(vv)]]);
# Now we obtain the Maxwell-Dirac equations:
a0:=map(x->diff(x,x0),psi);
a1:=map(x->diff(x,x1),psi);
a2:=map(x->diff(x,x2),psi);
a3:=map(x->diff(x,x3),psi);

e:=array(0..3):
for i from 0 to 3 do
    p:=cat(A,i)(vv):
    p2:=evalm(psi_b.cat(g,i).psi):
    e[i]:=diff(p,x0$2)-diff(p,x1$2)-diff(p,x2$2)-diff(p,x3$2)-p2[1,1]
od:
eq1:={e[0],e[1],e[2],e[3]}:
#r1:=liesymmetries(eq1,[A0(vv),A1(vv),A2(vv),A3(vv)]);


p0:=evalm(A0(vv)*g0-A1(vv)*g1-A2(vv)*g2-A3(vv)*g3);

r1:=evalm(I*(g0.a0+g1.a1+g2.a2+g3.a3)+m*psi-p0.psi):
eq2:=expand({r1[1,1],r1[2,1],r1[3,1],r1[4,1]});


eq3:=0:
for i from 0 to 3 do
    eq3:=eq3+diff(cat(A,i)(vv),cat(x,i))
od:
eq3:={eq3};

eqs:=expand(eq1 union eq2 union eq3):


# Real and imaginary parts of the equations, respectivelly:
eqs_r:=subs(I=0,eqs) minus {0};
eqs_i:=map(x->coeff(x,I),eqs) minus {0};


nops(eqs_r);
nops(eqs_i);


SADE[traceout]:=true;

# Computing Lie symmetries
t1:=time():
s1:=liesymmetries({op(eqs_r),op(eqs_i)},
         [u1(vv),u2(vv),u3(vv),u4(vv),
          v1(vv),v2(vv),v3(vv),v4(vv),
          A0(vv),A1(vv),A2(vv),A3(vv)]):
time()-t1;

nops(s1[1]);
# And the comutations table for the finite algebra (Note that ton of the generators
# is a particular element of the ifinite sub-lagebra):
s2:=eval(subs(_F1(x0, x1, x2, x3)=1/2,s1[1]));
com_table(s2,SADE[_vars],G);
quit

