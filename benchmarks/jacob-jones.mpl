#
# Jacob-Jones equation - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
# This is a special case that requires first the reduction of the determining system to involutive form.
#
with(sade):
eq:=diff(u(x,y,t),t)-(1/2)*a^2*x^2*diff(u(x,y,t),x,x)-a*b*c*x*y*diff(u(x,y,t),x,y)
-(1/2)*b^2*y^2*diff(u(x,y,t),y,y)-(d*x*log(y/x)-e*x^(3/2))*diff(u(x,y,t),x)
-(f*y*log(g/y)-h*y*x^(1/2))*diff(u(x,y,t),y)+x*u(x,y,t);
t1:=time():
s1:=liesymmetries(eq,[u(x,y,t)],involutive);
time()-t1;
quit
