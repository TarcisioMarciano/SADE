#
# Free Klein-Gordon equation with mass m - CRC Handbook - Lie Group Analysis
# of Differential Equations, Vol. 2, N.H. Ibragimov Ed, CRC Press (Boca Raton 1995).
#
with(sade):
eq:=diff(phi(x,y,z,t),x,x)+diff(phi(x,y,z,t),y,y)+diff(phi(x,y,z,t),z,z)
    -diff(phi(x,y,z,t),t,t)-m^2*phi(x,y,z,t);
t1:=time():
gens:=liesymmetries(eq,[phi(x,y,z,t)]);
time()-t1;
nops(gens[1]);
quit

