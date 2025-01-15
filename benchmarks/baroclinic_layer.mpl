#
# Equations of flows in baroclinic Layer of ocean - CRC Handbook Analysis of Differential Equations, Vol. 2,
# N. H. Ibragimov Ed., CRC Press (Boca Raton, 1995).
#
with(sade):
a:=x,y,z;
eqs:={diff(u(a),x)+diff(v(a),y)+diff(w(a),z)=0,
      u(a)*diff(rho(a),x)+v(a)*diff(rho(a),y)+w(a)*diff(rho(a),z)=diff(rho(a),x,x)+diff(rho(a),y,y)+diff(rho(a),z,z),
      diff(p(a),x)=1-x*v(a),diff(p(a),y)=-1+x*u(a),diff(p(a),z)=g*rho(a)};
t:=time():
gens:=liesymmetries(eqs,[u(a),v(a),w(a),rho(a),p(a)]);
time()-t;
quit
