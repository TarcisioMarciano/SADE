#
# 3D Wave equation - G.W. Bluman and S. Kumei, Symmetries and differential equations, Spinger-Verlag (New York, 1989)
#
with(sade):
eq:={diff(u(x,y,z,t),t,t)-diff(u(x,y,z,t),x,x)-diff(u(x,y,z,t),y,y)-diff(u(x,y,z,t),z,z)};
t1:=time():
s1:=liesymmetries(eq,[u(x,y,z,t)]);
t2:=time():
t2-t1;
nops(s1[1]);
