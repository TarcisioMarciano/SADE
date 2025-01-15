# Computing the Lie Symmetries of the Yang-Mills equations with SU(3) Gauge
with(sade):


# Dimension of the gauge algebra
ndim:=8;


# This routine defines the structure constants with the right symmetries from its non-reduntant values.
#
# Builds the structure constants in the array name ginven in a, with range 1..k,
# and symmtry given in sh (symmetric or antisymmetric). The values are specified in a.
#
buildstruct:=proc(a,nm,k)
local i,pr,p1,p2,p3,vl,ss:
nm:=rtable(1..k,1..k,1..k,fill=0):
ss:=-1:
for i from 1 to nops(a) do
    pr:=op(1,a[i]):
    vl:=op(2,a[i]):
    p1:=pr[1]:
    p2:=pr[2]:
    p3:=pr[3]:
    nm[p1,p2,p3]:=vl:
    nm[p1,p3,p2]:=ss*vl:
    nm[p2,p1,p3]:=ss*vl:
    nm[p2,p3,p1]:=vl:
    nm[p3,p1,p2]:=vl:
    nm[p3,p2,p1]:=ss*vl
od:
NULL
end:


# The non-redundant values are specified here. Other values not related to these are considered zero.
ff:=[[1,2,3]=1,[1,4,7]=1/2,[1,5,6]=-1/2,[2,4,6]=1/2,[2,5,7]=1/2,[3,4,5]=1/2,[3,6,7]=-1/2,
     [4,5,8]=sqrt(3)/2,[6,7,8]=sqrt(3)/2];

buildstruct(ff,e,8);

# Diagonal part of the metric.
g:=x->if x=0 then 1 else -1 fi:


# Here we obtain the Yang-Mills field tensor F(mu,nu,a):
#
# Building F -> mu e nu covariant
#
F:=table():
v:=x0,x1,x2,x3:
for mu from 0 to 3 do
for nu from 0 to 3 do
for a from 1 to ndim do
    p1:=cat(A,mu,a):
    p2:=cat(A,nu,a):
    p1:=p1(v):
    p2:=p2(v):
    F[mu,nu,a]:=diff(p2,cat(x,mu))-diff(p1,cat(x,nu)):
    for b from 1 to ndim do
    for c from 1 to ndim do
        p1:=cat(A,mu,b):
        p2:=cat(A,nu,c):
        p1:=p1(v):
        p2:=p2(v):
        F[mu,nu,a]:=F[mu,nu,a]+lambda*e(a,b,c)*p1*p2
    od
    od
od
od
od:


# And now the field equations:
eqs:={}:
for a from 1 to ndim do
for nu from 0 to 3 do
    p:=0:
    for mu from 0 to 3 do
        p:=p+diff(F[mu,nu,a],cat(x,mu))*g(mu):
        for b from 1 to ndim do
        for c from 1 to ndim do
            p2:=cat(A,mu,b):
            p2:=p2(v)*g(mu):
            p:=p+lambda*e(a,b,c)*p2*F[mu,nu,c]
        od
        od
    od:
    eqs:=eqs union {p}
od
od:
eqs:=simplify(eqs):


fields:={}:
for mu from 0 to 3 do
for a from 1 to ndim do
    fields:=fields union {cat(A,mu,a)(v)}
od
od:
fields:=[op(fields)];


nops(eqs);

nops(fields);


SADE[traceout]:=true;

# Computing Lie symmetries:
t1:=time():
gens:=liesymmetries(eqs,fields);
time()-t1;

nops(gens[1]);

quit

