#
# Magneto-hydo-Dynamics equations - W. Heremann "Symbolic software for Lie symmetry analysis",
# in CRC Handbook of Lie group analysis of differential equations, Vol. 1, pg. 7,
# N.H. Ibragimov Ed., CRC Press (Boca Raton, 1996).
#
with(sade):
w:=(x,y,z,t);
aa:=q(w)=p(w)+(h1(w)^2+h2(w)^2+h3(w)^2)/2;
eqs:={diff(r(w),t)+u1(w)*diff(r(w),x)+u2(w)*diff(r(w),y)+u3(w)*diff(r(w),z)+r(w)*(diff(u1(w),x)+diff(u2(w),y)+diff(u3(w),z)),
r(w)*(diff(u1(w),t)+u1(w)*diff(u1(w),x)+u2(w)*diff(u1(w),y)+u3(w)*diff(u1(w),z))+diff(q(w),x)-h1(w)*diff(h1(w),x)-h2(w)*diff(h1(w),y)-h3(w)*diff(h1(w),z),
r(w)*(diff(u2(w),t)+u1(w)*diff(u2(w),x)+u2(w)*diff(u2(w),y)+u3(w)*diff(u2(w),z))+diff(q(w),y)-h1(w)*diff(h2(w),x)-h2(w)*diff(h2(w),y)-h3(w)*diff(h2(w),z),
r(w)*(diff(u3(w),t)+u1(w)*diff(u3(w),x)+u2(w)*diff(u3(w),y)+u3(w)*diff(u3(w),z))+diff(q(w),z)-h1(w)*diff(h3(w),x)-h2(w)*diff(h3(w),y)-h3(w)*diff(h3(w),z),
diff(h1(w),x)+diff(h2(w),y)+diff(h3(w),z),
diff(h1(w),t)+u1(w)*diff(h1(w),x)+u2(w)*diff(h1(w),y)+u3(w)*diff(h1(w),z)+h1(w)*(diff(u1(w),x)+diff(u2(w),y)+diff(u3(w),z))
     -h1(w)*diff(u1(w),x)-h2(w)*diff(u1(w),y)-h3(w)*diff(u1(w),z),
diff(h2(w),t)+u1(w)*diff(h2(w),x)+u2(w)*diff(h2(w),y)+u3(w)*diff(h2(w),z)+h2(w)*(diff(u1(w),x)+diff(u2(w),y)+diff(u3(w),z))
     -h1(w)*diff(u2(w),x)-h2(w)*diff(u2(w),y)-h3(w)*diff(u2(w),z),
diff(h3(w),t)+u1(w)*diff(h3(w),x)+u2(w)*diff(h3(w),y)+u3(w)*diff(h3(w),z)+h3(w)*(diff(u1(w),x)+diff(u2(w),y)+diff(u3(w),z))
     -h1(w)*diff(u3(w),x)-h2(w)*diff(u3(w),y)-h3(w)*diff(u3(w),z),
diff(p(w),t)+k*p(w)*(diff(u1(w),x)+diff(u2(w),y)+diff(u3(w),z))+u1(w)*diff(p(w),x)+u2(w)*diff(p(w),y)+u3(w)*diff(p(w),z)};

eqs:=subs(aa,eqs);

t1:=time():
gens:=liesymmetries(eqs,[p(w),r(w),u1(w),u2(w),u3(w),h1(w),h2(w),h3(w)]);
time()-t1;

nops(gens[1]);

com_table(gens[1],SADE[_vars],G);
quit




