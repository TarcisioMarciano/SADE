#
# Non-linear telegraphi equation - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
eqs:={diff(v(x,t),t)-diff(u(x,t),x),-diff(v(x,t),x)-f(u(x,t))*diff(u(x,t),t)-g(u(x,t))};
t1:=time():
s1:=liesymmetries(eqs,[u(x,t),v(x,t)],[x,t]);
t2:=time():
t2-t1;
nops(s1[1]);
quit

