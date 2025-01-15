#
# Maxwell equations - CRC Handbook - Lie Group Analysis
# of Differential Equations, Vol. 2, N.H. Ibragimov Ed, CRC Press (Boca Raton 1995).
#
with(sade):
with(VectorCalculus):
SetCoordinates( 'cartesian'[x,y,z] );
E := VectorField( <Ex(x,y,z,t),Ey(x,y,z,t),Ez(x,y,z,t)> );
B := VectorField( <Bx(x,y,z,t),By(x,y,z,t),Bz(x,y,z,t)> );
Divergence(E);
eq1:=Divergence(E);
eq2:=Curl(E)+diff(B,t);
eq3:=Divergence(B);
eq4:=c^2*Curl(B)-diff(E,t);
eqs:={eq1,eq2[1],eq2[2],eq2[3],eq3,eq4[1],eq4[2],eq4[3]};
funcs:=[E[1],E[2],E[3],B[1],B[2],B[3]];
t1:=time():
s1:=liesymmetries(eqs,funcs);
time()-t1;
nops(s1[1]);

