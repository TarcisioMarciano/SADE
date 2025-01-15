#
# 3D Burgers equation
#
with(sade):
eqx:=diff(ux(x,y,z,t),t)+ux(x,y,z,t)*diff(ux(x,y,z,t),x)+uy(x,y,z,t)*diff(ux(x,y,z,t),y)+uz(x,y,z,t)*diff(ux(x,y,z,t),z)
    -nu*(diff(ux(x,y,z,t),x,x)+diff(ux(x,y,z,t),y,y)+diff(ux(x,y,z,t),z,z));
eqy:=diff(uy(x,y,z,t),t)+ux(x,y,z,t)*diff(uy(x,y,z,t),x)+uy(x,y,z,t)*diff(uy(x,y,z,t),y)+uz(x,y,z,t)*diff(uy(x,y,z,t),z)
    -nu*(diff(uy(x,y,z,t),x,x)+diff(uy(x,y,z,t),y,y)+diff(uy(x,y,z,t),z,z));
eqz:=diff(uz(x,y,z,t),t)+ux(x,y,z,t)*diff(uz(x,y,z,t),x)+uy(x,y,z,t)*diff(uz(x,y,z,t),y)+uz(x,y,z,t)*diff(uz(x,y,z,t),z)
    -nu*(diff(uz(x,y,z,t),x,x)+diff(uz(x,y,z,t),y,y)+diff(uz(x,y,z,t),z,z));
t1:=time():
s1:=liesymmetries({eqx,eqy,eqz},[ux(x,y,z,t),uy(x,y,z,t),uz(x,y,z,t)]);
time()-t1;
nops(s1[1]);
