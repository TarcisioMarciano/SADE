#
# von Karman equations - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
eqs:={diff(f(x,y,t),x,x,x,x)+diff(f(x,y,t),y,y,y,y)+2*diff(f(x,y,t),x,x,y,y)-
          diff(w(x,y,t),y,x)^2+diff(w(x,y,t),x,x)*diff(w(x,y,t),y,y),
      diff(w(x,y,t),x,x,x,x)+diff(w(x,y,t),y,y,y,y)+2*diff(w(x,y,t),x,x,y,y)+diff(w(x,y,t),t,t)-
          diff(f(x,y,t),y,y)*diff(w(x,y,t),x,x)-
      diff(f(x,y,t),x,x)*diff(w(x,y,t),y,y)+2*diff(f(x,y,t),y,x)*diff(w(x,y,t),y,x)};
t1:=time():
s1:=liesymmetries(eqs,[f(x,y,t),w(x,y,t)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit

