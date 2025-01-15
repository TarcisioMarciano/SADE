#
# TRansoni equations - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
eq:={diff(u(x,y),y)=diff(v(x,y),x),diff(v(x,y),y)=-u(x,y)*diff(u(x,y),x)};
t1:=time():
s1:=liesymmetries(eq,[u(x,y),v(x,y)]);
time()-t1;
nops(s1[1]);
quit
