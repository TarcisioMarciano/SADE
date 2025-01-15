#
# Navier-Stokes equations - G.W. Bluman and S. Kumei, Symmetries and differential equations, Spinger-Verlag (New York, 1989)
#
with(sade):
printlevel:=2;

eq:={diff(u(x,y,z,t),t)+u(x,y,z,t)*diff(u(x,y,z,t),z)+v(x,y,z,t)*diff(u(x,y,z,t),x)+
  w(x,y,z,t)*diff(u(x,y,z,t),y)+diff(s(x,y,z,t),z)-a*(diff(u(x,y,z,t),z,z)+diff(u(x,y,z,t),x,x)+diff(u(x,y,z,t),y,y)),
diff(v(x,y,z,t),t)+u(x,y,z,t)*diff(v(x,y,z,t),z)+v(x,y,z,t)*diff(v(x,y,z,t),x)+w(x,y,z,t)*diff(v(x,y,z,t),y)+
  diff(s(x,y,z,t),x)-a*(diff(v(x,y,z,t),z,z)+diff(v(x,y,z,t),x,x)+diff(v(x,y,z,t),y,y)),
diff(w(x,y,z,t),t)+u(x,y,z,t)*diff(w(x,y,z,t),z)+v(x,y,z,t)*diff(w(x,y,z,t),x)+w(x,y,z,t)*diff(w(x,y,z,t),y)+
  diff(s(x,y,z,t),y)-a*(diff(w(x,y,z,t),z,z)+diff(w(x,y,z,t),x,x)+diff(w(x,y,z,t),y,y)),
diff(u(x,y,z,t),z)+diff(v(x,y,z,t),x)+diff(w(x,y,z,t),y)};
t1:=time():
s1:=liesymmetries(eq,[u(x,y,z,t),v(x,y,z,t),w(x,y,z,t),s(x,y,z,t)]);
t2:=time():
t2-t1;
nops(s1[1]);
quit

