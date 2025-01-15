#
# Heat diffusion equation - P. OLver, Applications of Lie Groups to Differential Equations,
# 2nd Ed, Springer-Verlag (new York, 1991).
#
with(sade):
eq:={diff(u(y,t),t)-nu*diff(u(y,t),y,y)};
t1:=time():
s1:=liesymmetries(eq,[u(y,t)]);
t2:=time():
t2-t1;
nops(s1[1]);
