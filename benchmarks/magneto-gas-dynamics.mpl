#
# Magneto-gas-dynamics equations - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
eq:={diff(r(x,t),t)+diff(r(x,t),x)*u(x,t)+r(x,t)*diff(u(x,t),x),
      diff(b(x,t),t)+u(x,t)*diff(b(x,t),x)+b(x,t)*diff(u(x,t),x),
      r(x,t)*(diff(u(x,t),t)+u(x,t)*diff(u(x,t),x))+diff(p(x,t),x)+(1/a)*(b(x,t)*diff(b(x,t),x)),
      diff(p(x,t),t)+u(x,t)*diff(p(x,t),x)-(c*p(x,t)/r(x,t))*(diff(r(x,t),t)+u(x,t)*diff(r(x,t),x))};
t1:=time():
s1:=liesymmetries(eq,[u(x,t),r(x,t),b(x,t),p(x,t)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit
