#
# Kadomtsev-Petviashvili equation - G.W. Bluman and S. Kumei, Symmetries and differential equations, Spinger-Verlag (New York, 1989)
with(sade):
printlevel:=2;
eq:={diff(u(x,y,z),y,y,y,y)+3*diff(u(x,y,z),z,z)+6*u(x,y,z)*diff(u(x,y,z),y,y)+4*diff(u(x,y,z),y,x)+6*diff(u(x,y,z),y)^2};
t1:=time():
s1:=liesymmetries(eq,[u(x,y,z)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit

