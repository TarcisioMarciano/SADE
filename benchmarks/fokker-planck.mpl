#
# 1D Fokker-Planck equation - G.W. Bluman and S. Kumei, Symmetries and differential equations, Spinger-Verlag (New York, 1989)
#
with(sade):
eq:={diff(u(x,t),t)-diff(u(x,t),x,x)+x*diff(u(x,t),x)+u(x,t)};
t1:=time():
s1:=liesymmetries(eq,[u(x,t)]);
t2:=time():
t2-t1;
nops(s1[1]);
