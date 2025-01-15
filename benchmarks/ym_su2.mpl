#
# Yang Mills field equations with WU(2) gauge group - F. Schwarz, Lett. Math. Phys. 6 (1982) 355.
#
restart;
with(sade):
e:=proc(a,b,c)
if a=b or b=c or a=c then RETURN(0) fi:
if a=1 then
   if b=2 and c=3 then RETURN(1) else RETURN(-1) fi
fi:
if a=2 then
   if b=1 and c=3 then RETURN(-1) else RETURN(1) fi
fi:
if a=3 then
   if b=1 and c=2 then RETURN(1) else RETURN(-1) fi
fi
end:   
g:=proc(a,b)
if a<>b then RETURN(0) fi:
if a=0 then RETURN(1) fi:
-1
end:
#
# F -> mu e nu em cima (contravariante)
# F -> mu e nu em baixo (covariante)
#
F:=table():
F2:=table():
v:=x0,x1,x2,x3:
for mu from 0 to 3 do
for nu from 0 to 3 do
for a from 1 to 3 do
    p1:=cat(A,mu,a):
    p2:=cat(A,nu,a):
    p1:=p1(v):
    p2:=p2(v):
    F[mu,nu,a]:=diff(p2,cat(x,mu))-diff(p1,cat(x,nu)):
    for b from 1 to 3 do
    for c from 1 to 3 do
        p1:=cat(A,mu,b):
        p2:=cat(A,nu,c):
        p1:=p1(v):
        p2:=p2(v):
        F[mu,nu,a]:=F[mu,nu,a]-lambda*e(a,b,c)*p1*p2
    od
    od:
    F2[mu,nu,a]:=g(mu,mu)*g(nu,nu)*F[mu,nu,a]
od
od
od:
eqs:={}:
for a from 1 to 3 do
for nu from 0 to 3 do
    p:=0:
    for mu from 0 to 3 do
        p:=p+diff(F2[mu,nu,a],cat(x,mu)):
        for b from 1 to 3 do
        for c from 1 to 3 do
            p2:=cat(A,mu,b):
            p2:=p2(v):
            p:=p-lambda*e(a,b,c)*p2*F2[mu,nu,c]
        od
        od
    od:
    eqs:=eqs union {p}
od
od:
eqs:=simplify(eqs):
fields:={}:
for mu from 0 to 3 do
for a from 1 to 3 do
    fields:=fields union {cat(A,mu,a)(v)}
od
od:
fields:=[op(fields)];
nops(eqs);


#SADE[traceout]:=true;
t1:=time();
gens:=liesymmetries(eqs,fields);
time()-t1;
nops(gens[1]);
quit
