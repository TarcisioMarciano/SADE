#
# Vaidya equations - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
eq:={diff(v(x,y,z),z)+u(x,y,z)*sin(y)*diff(u(x,y,z),x)-
         v(x,y,z)*sin(y)*diff(v(x,y,z),x)+sin(y)*diff(u(x,y,z),y)-u(x,y,z)*cos(y),
     diff(u(x,y,z),z)-u(x,y,z)*sin(y)*diff(v(x,y,z),x)-
        v(x,y,z)*sin(y)*diff(u(x,y,z),x)-sin(y)*diff(v(x,y,z),y)+v(x,y,z)*cos(y)};
#SADE[traceout]:=true;
t1:=time():
s1:=liesymmetries(eq,[u(x,y,z),v(x,y,z)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit
