#
# Euler inviscid flow equations - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
eqs:={diff(u(x,y,z,t),t)+u(x,y,z,t)*diff(u(x,y,z,t),x)+v(x,y,z,t)*diff(u(x,y,z,t),y)+
          w(x,y,z,t)*diff(u(x,y,z,t),z)+diff(p(x,y,z,t),x),
      diff(v(x,y,z,t),t)+u(x,y,z,t)*diff(v(x,y,z,t),x)+v(x,y,z,t)*diff(v(x,y,z,t),y)+
          w(x,y,z,t)*diff(v(x,y,z,t),z)+diff(p(x,y,z,t),y),
      diff(w(x,y,z,t),t)+u(x,y,z,t)*diff(w(x,y,z,t),x)+v(x,y,z,t)*diff(w(x,y,z,t),y)+
          w(x,y,z,t)*diff(w(x,y,z,t),z)+diff(p(x,y,z,t),z),
      diff(u(x,y,z,t),x)+diff(v(x,y,z,t),y)+diff(w(x,y,z,t),z)};
t1:=time():
s1:=liesymmetries(eqs,[u(x,y,z,t),v(x,y,z,t),w(x,y,z,t),p(x,y,z,t)]);
t2:=time():
t2-t1;
nops(s1[1]);
