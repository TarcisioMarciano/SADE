#
# Burgers equation - P. Olver, Applications of Lie Grupos to Differential Equations,
# 2nd Ed, Springer-Verlag (new York, 1991).
#
with(sade):
eq:={diff(u(x,y),x,x)-diff(u(x,y),y)-u(x,y)*diff(u(x,y),x)};
t1:=time():
s1:=liesymmetries(eq,[u(x,y)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit
