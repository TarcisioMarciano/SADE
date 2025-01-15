#
# Non-linear Schroedinger equation - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
eqs:={diff(u(x,t),t)+diff(v(x,t),x,x)+2*v(x,t)*(u(x,t)^2+v(x,t)^2),
      -diff(v(x,t),t)+diff(u(x,t),x,x)+2*u(x,t)*(u(x,t)^2+v(x,t)^2)};
t1:=time():
s1:=liesymmetries(eqs,[u(x,t),v(x,t)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit

