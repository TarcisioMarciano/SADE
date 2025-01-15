#
# Equations of migration of melt through the mantle of the earth -
# CRC Handbook Analysis of Differential Equations, Vol. 2,
# N. H. Ibragimov Ed., CRC Press (Boca Raton, 1995).
#
with(sade):
eq:=diff(phi(z,t),t)+diff(phi(z,t)^n*(1-diff(diff(phi(z,t),t)/phi(z,t)^m,z)),z);
t1:=time():
gens:=liesymmetries(eq,[phi(z,t)]);
time()-t1;
quit
