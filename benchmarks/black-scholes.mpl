#
# Black-Scholes equation - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
eq:={diff(u(x,t),t)+(1/2)*a^2*x^2*diff(u(x,t),x,x)+b*x*diff(u(x,t),x)-c*u(x,t)};
t1:=time():
s1:=liesymmetries(eq,[u(x,t)]);
t2:=time():
t2-t1;
nops(s1[1]);

