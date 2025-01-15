#
# 3D Fokker-Planck Equation - J. Butcher, J. Carminato and K.T. Vu, Comp. Phys. Comm. 155 (2003) 92.
#
with(sade):
eq:={diff(u(x,y,t),t)=diff(u(x,y,t),x,x)+diff(u(x,y,t),y,y)+x*diff(u(x,y,t),x)+y*diff(u(x,y,t),y)+u(x,y,t)};
t1:=time():
s1:=liesymmetries(eq,[u(x,y,t)]);
t2:=time():
t2-t1;
nops(s1[1]);

