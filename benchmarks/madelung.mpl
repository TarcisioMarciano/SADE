#
# Madelund fluid equations - G.W. Bluman and S. Kumei, Symmetries and differential equations, Spinger-Verlag (New York, 1989)
#
with(sade):
eq:={diff(u(x,y),y)+(1/2)*diff(u(x,y),x)^2+2*v(x,y)-2*x+(1/(2*v(x,y)^2))*diff(v(x,y),x)^2-(1/v(x,y))*diff(v(x,y),x,x),
      diff(v(x,y),y)+diff(v(x,y),x)*diff(u(x,y),x)+v(x,y)*diff(u(x,y),x,x)};
SADE[traceout]:=true;
t1:=time():
s1:=liesymmetries(eq,[u(x,y),v(x,y)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit
