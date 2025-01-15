# SADE - Symmetry Analysis of Differential Equations
# 
#  Version 4.1a2
# 
# Tarcisio Marciano da Rocha Filho*
# and
# Annibal Dias de Figueiredo Neto
# 
# Instituto de Fisica - Universidade de Brasilia
# and
# International Center for Condensed Matter Physics - ICCMP (BRAZIL)
# 
# *marciano@fis.unb.br
# 
# First Version - December 27, 1994.

# Last major modifications:
#    
# September 28, 2002 - November 3, 2003 - January 5, 2004 -
# August 16, 2004 - November 22,  2005.
# August, 10 2006, January, 05 2007; May 29, 2007; January, 6 2010.
# April, 17 2011.
# 
# Last modification: May 4, 2023.

# Introduction
# This package have been developed at the Physics Institute at the University of Brasilia / BRAZIL since circa 1994.
# Initially developed by T. M. Rocha Filho (marciano@fis.unb.br), it was expanded continously during the last 15 years
# in colaboration with A. Figueiredo (QPSI module).
# Implementation - Initialization
# Initialization
restart:
sade := module()
export liesymmetries,comm,com_table,casimir_invariant,ansatz,reduce_ode_sist,issolvable,odesolver,invariant_sol,
       noether,QPsymmetries,conserved,constlog,lindsolve,ode_invsolution,ode_reduce_order1,nldsolve,
       canonical_basis,derived_subalg,nonlindsolve,ncsymmetries,verif_if_inv,equivalence,linear_rep,
       StructConst,AdjointRep,LBsymmetries,PDEreduction,invariant_cond,

setcont,sizeorder,orthoform,clean_eqs:

local

eqsimm,extend_gen,init,resolve,resolve2,ritred,algsimp,odesimp1,decompfnc,
diffsolve,pdiffsolve,odesimpv,
algsimpdiff,varcompat,searchfunction,
var_int,int_subs,lifdec,lifunc,rpsub,iint,
intsimp,whichder,whichder2,inlist,whichderlist,isitinteg,whichdervar,
derdeg,tautoelim,simpfunc,integeq,symmetries,infsym,coeffgen,eqtab,
uptoone,dtot,funcdep,wder,conv,replace,posvars,sym_generators,d_tot,noether_inv,
nt_inv,nt_comp_inv,polyn,twodim_cancoord,charcrt,whichFarg,regpds,pdsolve_c,
nlpdsolve,simpeqd,genred,livec,gaussolv,dtot2,
isdiffgt,highestdiff,subsexp,solvhigh,subsdom,subsdom_simp,
orddiff,subeq,listdiff,listminus,tonuple,whichderlist2,gtlex,sizeorder2,
LVformat,eqToCauchy,isQM,isQP,algsys,pcont,prod,matrix_prod,polyn_hom,
quasisyst,simp_sqrt,quasisolve,paramcont,ccont,C_Ccont,Ucont,xcont,invsearch,
cleansolve,cleansolution,clean_all,final_form,test_constcoeff,ext_solve,
moncoeff,newfactor,varblspos,LKform,numterm,cont,LieDeriv,nuplesequence,
tensordeteq,invariant_tensor,arrayfactor,arraysimplify,inv_verif,semi_inv_verif,
semi_inv_aux,take_out,general_poly,genmonom,newquasisyst,homog_poly_syst,
newinv,newinvariants,coeff_hom_syst,coeff_hom,is_ord,
diag_lin,arrange_solution,arrsol,param_only,param_only2,ccont2,keep_not_c,
c_solve,coordtr,matreorg,geom_meth_inv,geom_meth_aux,ld_meth_inv,ld_meth_aux,
rat_meth_aux,solinvert,invariant,tau_solve,polyn_cmpt,poly_inv_log,polylog_inv,
lifdec2,lifunc2,rpsub2,reglzeq,morevars,highcoeff,
iseqlin,sym_nonclassical,noncl_generators,equiv_aux,
simpprod,simpbynd,safesubs,subsord,funcoeff,pppdsolve,indepord,solvlinsyst,nonlinli,
singlelinsolve,nonlinodesolve,genlinsolve,gennlsolve,funcrellin,singlered,
compatred,pegaperm,umcomprox,umnosoutros,polydec,funcdecomp,nlalgdiff,
singlediffsolve,whichfunction,regular_diff,partial_involutive,regularize_eq,
uniform_function,conv_diff,whoisdiff,suball,setcontonly,lowestdiff_var,bestdiff,
bestdiffvar,nclass_det,whichder3,isdiffgt_purelex,countvarlist,diffcoeff,
dspoly,pseudored,pseudonormal,KolchinRittSort,KolchinRitt,nonlinsolveeq,orderfunctions,
singlesolve,which_der_present,single_diff_single_var,invol_compat,build_poly,newsolve:

option package, load = init:

init := proc()
global SADE:
print():
print(`Symmetry Analysis of Differential Equations`):
print(`By Tarcisio M. Rocha Filho - Annibal Figueiredo - 2013`):
print():
protect(determining,parameters,positive,transformation):
with(combinat,choose): 
with(linalg):
with(Groebner):
with(DEtools,rifsimp):
SADE[_GB]:=false:
with(combinat,permute):
with(linalg):
SADE[nored]:=false:
SADE[cmax]:=1:
SADE[ccount]:=1:
SADE[addcond]:={}:
SADE[_addrules]:={}:
SADE[__U]:=U:
SADE[_tt]:=_tt:
SADE[_C]:=_b:
SADE[_c]:=_a:
SADE[_subsflag]:=false:
SADE[_timel]:=20:
SADE[_nmaxeq]:=8:
SADE[traceout]:=false:
SADE[_maxeqjanet]:=5:
SADE[_timeinvol]:=-1:
SADE[_difforder]:=_tdeglex:
SADE[_KCincrement]:=3:
SADE[partial_reduction]:=5:
SADE[_num_partial_inv]:=50000:
SADE[_ne]:=5:
SADE[_algdiff]:=50:
SADE[_compatnoeqs]:={}:
end:

# Implementation - ODSS (Over-Determined Systems Solver)
# lindsolve
#
# Solves a set of linear differential equations in the set eqs and and in the
# unknown functions set unks.
#
lindsolve:=proc(eqs,unks)
local i,n1,n2,dep,indep,unknowns,res,prov,prov2,prov3:
global SADE:
SADE[_compatnoeqs]:={}:
unknowns:=[op(unks)]:
dep:=map(x->op(0,x),unks):
dep:=[op(dep)]:
indep:={}:
for i from 1 to nops(unks) do
    indep:=indep union {op(unks[i])}
od:
indep:=[op(indep)]:
#SADE[_system]:=[eqs,unks,{}]:
SADE[_depvars]:=dep:
SADE[_indepvars]:=indep:
SADE[fcount]:=1:
SADE[fname]:=_q:
SADE[incognita]:={op(unks)}:
SADE[var]:=[op(dep),op(indep)]:
SADE[_vars]:=SADE[var]:
if nargs=3 then
   SADE[_vars]:=args[3]
fi:
SADE[_decompvar]:=SADE[var]:
SADE[_system]:=[eqs,unknowns,{}]:
resolve():
res:={}:
for i from 1 to nops(unknowns) do
res:=res union {unknowns[i]=SADE[_system][2][i]}
od:
prov3:=SADE[_system][1] minus {0}:
n1:=1:
n2:=1:
for i from 1 to SADE[fcount] do
    prov:=cat(SADE[fname],i):
    if has(res,prov) then
       prov2:=SADE[incognita] intersect {prov}:
       if prov2={} then
          prov2:=cat(_F,n1):
          n1:=n1+1
       else
          prov2:=cat(_C,n2):
          n2:=n2+1
       fi:
       res:=subs(prov=prov2,res):
       prov3:=subs(prov=prov2,prov3)
    fi
od:
if prov3<>{} then
   res:=[res,prov3]
fi:
res
end:
# resolve
#
# Solves the determining system using the implemented routine for solving equations.
# Calling command:  resolve()
#
resolve:=proc()
local f,f2,f3,ne,old:
global SADE:
f2:=false:
f3:=false:
if SADE[traceout]=true then
   print(`Trying to solve an algebraic equation with at most 2 terms...`):
   print(``)
fi:
algsimp(2):
old:=SADE[_system]:
SADE[_flag]:=true:
if SADE[traceout]=true then
   print(`Trying to solve a single term ODE... `):
   print(``)
fi:
f:=singlediffsolve():
if f then SADE[_flag]:=true fi:
while f do f:=singlediffsolve() od:
if nops(SADE[_system][1])<SADE[_algdiff] and setcont(SADE[incognita],SADE[_unks0])<>{} then
   if SADE[traceout]=true then
      print(`Trying to solve an algebraic equation in the original unknowns... `):
      print(``)
   fi:
   f:=algsimpdiff(SADE[_unks0]):
   while f do f:=algsimpdiff(SADE[_unks0]) od
fi:
#if SADE[_partial_inv]<>false and SADE[_partial_inv_first]=true then
if SADE[_partial_inv]<>false then
#   decompfnc():
   partial_involutive(SADE[_partial_inv]):
   SADE[_partial_inv_first]:=false
fi:
while not(f2) do
      if SADE[traceout]=true then
         print(`Trying to decompose as an expansion in L. I. functions...`):
         print(``)
      fi:
      funcdecomp():
      if SADE[traceout]=true then
         print(`Trying to solve a single term ODE... `):
         print(``)
      fi:
      f:=singlediffsolve():
      f2:=f:
      if f then SADE[_flag]:=true fi:
      while f do f:=singlediffsolve() od:
      if f2 then
         resolve2()
      else
         #SADE[_system]:=old:
          if SADE[_system][1]<>{} then
            f:=ritred(SADE[_system][1],setcont(SADE[_system][1],SADE[incognita]))
         else
            RETURN()
         fi:
         SADE[_flag]:=false:
         if f<>false then
            SADE[_system][1]:=f:
            resolve2()
         fi
      fi:
      SADE[_system][1]:=simplify(SADE[_system][1]) minus {0}:
      if SADE[_system][1]={} then RETURN() fi:
      while not(f2) do
            ne:=SADE[_ne]:
            while not(f2) and ne<=SADE[_nmaxeq] do
                  if SADE[traceout]=true then
                     print(`Trying to solve an ODE with at most`,ne,`terms...`):
                     print(``)
                  fi:
                  f:=diffsolve(ne):
                  f2:=f:
                  if f then SADE[_flag]:=true fi:
                  while f do f:=diffsolve(ne) od:
                  if not(f2) then ne:=ne+3 fi
            od:
            if SADE[traceout]=true and ne=11 then
               print(`No ODE solved...`):
               print(``)
            fi:
            if f2 then RETURN(resolve2()) fi:
            f3:=compatred():
            if f3 then
               RETURN(resolve())
            fi:
            if SADE[traceout]=true then
               print(`Trying to solve an ODE with any number of terms...`):
               print(``)
            fi:
            f2:=diffsolve():
            if f2 then
               RETURN(resolve())
            else
               RETURN(resolve2())
            fi
      od:
      f2:=false
od:
end:
# resolve2
#
# Solves the determining system using a simpler algorithm than resolve for solving equations.
#
resolve2:=proc()
local f,f2,f3,f4,ne:
global SADE:
f2:=false:
f3:=false:
#SADE[_system][1]:=expand(map(x->numer(x),SADE[_system][1])):
if SADE[traceout]=true then
   print(`Expanding the dermining system...`):
   print(``)
fi:
SADE[_system][1]:=expand(SADE[_system][1]):
if SADE[traceout]=true then
   print(`Trying to solve an algebraic equation with at most 2 terms...`):
   print(``)
fi:
f:=algsimp(2):
while f do f:=algsimp(2) od:
while not(f2) do
      if SADE[traceout]=true then
         print(`Trying to decompose as an expansion in L. I. functions...`):
         print(``)
      fi:
      f2:=funcdecomp():
      if f2 then
         if SADE[traceout]=true then
            print(`Trying to solve an algebraic equation with at most 2 terms...`):
            print(``)
         fi:
         f:=algsimp(2):
         while f do f:=algsimp(2) od
      fi:
      if SADE[traceout]=true then
         print(`Trying to solve a single term ODE... `):
         print(``)
      fi:
      f:=singlediffsolve():
      f2:=f:
      if f then SADE[_flag]:=true fi:
      while f do f:=singlediffsolve() od:
      if f2 then RETURN(resolve2()) fi:
      while not(f2) do
            ne:=SADE[_ne]:
            while not(f2) and ne<=SADE[_nmaxeq] do
                  if SADE[traceout]=true then
                     print(`Trying to solve an ODE with at most`,ne,`terms...`):
                     print(``)
                  fi:
                  f:=diffsolve(ne):
                  f2:=f:
                  if f then SADE[_flag]:=true fi:
                  while f do f:=diffsolve(ne) od:
                  if not(f2) then ne:=ne+3 fi
            od:
            if SADE[traceout]=true and ne>SADE[_nmaxeq] then
               print(`No ODE solved...`):
               print(``)
            fi:
            if f2 then RETURN(resolve2()) fi:
                 while not(f2) do
                        if SADE[traceout]=true then
                           print(`Trying to solve an algebraic equation...`):
                           print(``)
                        fi:
                        f:=traperror(algsimp()):
                        if f=lasterror then f:=false fi:
                        f2:=f:
                        if f then SADE[_flag]:=true fi:
                        while f do
                              f:=algsimp():
                              if f=lasterror then
                                 f:=false
                              fi
                        od:
                        if f2 then RETURN(resolve2()) fi:
                        if SADE[_flag] then
                           SADE[_system][1]:=simplify(SADE[_system][1]) minus {0}:
                           if SADE[_system][1]={} then RETURN() fi:
                           f3:=ritred(SADE[_system][1],setcont(SADE[_system][1],SADE[incognita])):
                           SADE[_flag]:=false:
                           if f3<>false then
                              SADE[_system][1]:=f3:
                              RETURN(resolve2())
                           else
                              f3:=compatred():
                              if f3 then
                                 RETURN(resolve2())
                              fi:
                              if SADE[traceout]=true then
                                 print(`Trying to solve an ODE with any number of terms...`):
                                 print(``)
                              fi:
                              f3:=diffsolve():
                              #f4:=f3:
                              #while f4 do f4:=diffsolve() od:
                              if f3=false then
                                 RETURN()
                              fi
                           fi
                        else
                           if SADE[traceout]=true then
                              print(`Trying to solve an ODE with any number of terms...`):
                              print(``)
                           fi:
                           f:=diffsolve():
                           #while f do f:=diffsolve() od:
                           SADE[_flag]:=true 
                        fi:
                        if not(f3) then RETURN() fi
                  od:
                  f2:=false:
           # od:
            f2:=false
      od:
      f2:=false
od:
end:
# iseqlin
#
# Tests (true or false) if the equation in eq is linear in each function in v.
#
iseqlin:=proc(eq,v2)
local i,d,wd,u,v,u2,_v,p,p2,eq2:
u:={}:
v:={}:
u2:={}:
for i from 1 to nops(v2) do
    if type(v2[i],function) then
       u:=u union {op(0,v2[i])}:
       v:=v union {op(v2[i])}
    else
       u2:=u2 union {v2[i]}
    fi
od:
u:=[op(u)]:
v:=[op(v)]:
wd:=map(x->x[1],orddiff(whichder(eq),u,v)):
p:={}:
eq2:=eq:
for i from 1 to nops(wd) do
    eq2:=subs(wd[i]=cat(_v,i),eq2):
    p:=p union {cat(_v,i)}
od:
for i from 1 to nops(v2) do
    eq2:=subs(v2[i]=cat(_v,i+nops(wd)),eq2):
    p:=p union {cat(_v,i+nops(wd))}
od:
p2:=map(x->degree(eq2,x),[op(p)]):
for i from 1 to nops(p) do
    if p2[i]=FAIL or p2[i]<0 or p2[i]>1 then RETURN(false) fi
od:
p2:=map(x->ldegree(eq2,x),[op(p)]):
for i from 1 to nops(p) do
    if p2[i]=FAIL or p2[i]<0 or p2[i]>1 then RETURN(false) fi
od:
if traperror(degree(eq2,p))=1 or traperror(degree(eq2,p))=0 then RETURN(true) fi:
false
end:
# ritred
#
# Transforms the determining system into an involutive form using the DEtools[rifsimp]
#
ritred:=proc(eqs,funcs)
local i,res,res2,old,flag,prov:
global SADE:
if SADE[_system][1] minus {0}={} then RETURN(false) fi:
res:=convert(eqs,diff) minus {0}:
old:=res:
if SADE[traceout]=true then
   print(` `):print(`Trying to reduce the determining system...`)
fi:
#########
if SADE[_partial_inv]<>false then
   res:={op(SADE[_system][1])}:
   partial_involutive(SADE[_partial_inv]):
   res2:=map(x->numer(x),{op(SADE[_system][1])}):
   if res<>res2 then
      RETURN(res2)
   fi
fi:
#########
if not(type(SADE[_freefunctions],set)) or setcont(res,SADE[_freefunctions])={} then
   res:=traperror(DEtools[rifsimp](res,convert(setcont(res,funcs),list))):
   if res<>lasterror then
      res:=invol_compat(res[Solved]):
      SADE[incognita]:=SADE[incognita] union res[2]:
      res:=res[1]:
      #res:=map(x->op(1,x)-op(2,x),convert(res[Solved],set)):
      flag:=true:
   else
      if res="system is inconsistent" then
         ERROR(res)
      fi:
      if res="simplification only implemented for integer exponents" then
         old:=simplify(old):
         res:=traperror(DEtools[rifsimp](res,convert(setcont(old,funcs),list))):
         if res=lasterror then
            if res="system is inconsistent" then
               ERROR(res)
            fi:
            res=old:
            flag:=false
         else
            res:=map(x->op(1,x)-op(2,x),convert(res[Solved],set)):
            flag:=true
         fi
      else
         flag:=false
      fi:
   fi
else
   flag:=false
fi:
if SADE[traceout]=true then
   if res<>old and flag then
      print(`Reduced the system to an involutive form`):print(` `)
   else
      print(`No changes made...`):print(` `)
   fi
fi:
if flag then
   RETURN(res)
else
   RETURN(false)
fi
end:ritred:=proc(eqs,funcs)
local i,res,res2,old,flag,prov:
global SADE:
if SADE[_system][1] minus {0}={} then RETURN(false) fi:
res:=convert(eqs,diff) minus {0}:
old:=res:
if SADE[traceout]=true then
   print(` `):print(`Trying to reduce the determining system...`)
fi:
#########
if SADE[_partial_inv]<>false then
   res:={op(SADE[_system][1])}:
   partial_involutive(SADE[_partial_inv]):
   res2:=map(x->numer(x),{op(SADE[_system][1])}):
   if res<>res2 then
      RETURN(res2)
   fi
fi:
#########
if not(type(SADE[_freefunctions],set)) or setcont(res,SADE[_freefunctions])={} then
   res:=traperror(DEtools[rifsimp](res,convert(setcont(res,funcs),list))):
   if res<>lasterror then
      res:=invol_compat(res[Solved]):
      SADE[incognita]:=SADE[incognita] union res[2]:
      res:=res[1]:
#      res:=map(x->op(1,x)-op(2,x),convert(res[Solved],set)):
      flag:=true:
   else
      if res="system is inconsistent" then
         ERROR(res)
      fi:
      if res="simplification only implemented for integer exponents" then
         old:=simplify(old):
         res:=traperror(DEtools[rifsimp](res,convert(setcont(old,funcs),list))):
         if res=lasterror then
            if res="system is inconsistent" then
               ERROR(res)
            fi:
            res=old:
            flag:=false
         else
            res:=map(x->op(1,x)-op(2,x),convert(res[Solved],set)):
            flag:=true
         fi
      else
         flag:=false
      fi:
   fi
else
   flag:=false
fi:
if SADE[traceout]=true then
   if res<>old and flag then
      print(`Reduced the system to an involutive form`):print(` `)
   else
      print(`No changes made...`):print(` `)
   fi
fi:
if flag then
   RETURN(res)
else
   RETURN(false)
fi
end:
# invol_compat
invol_compat:=proc(eqs)
local i,res,le,ld,v1,v2,pr,vr,vi,add_eqs,add_unks,nm:
global SADE:
add_eqs:={}:
add_unks:={}:
res:={}:
for i from 1 to nops(eqs) do
    pr:=eqs[i]:
    le:=op(1,pr):
    ld:=op(2,pr):
    v1:=setcont(le,SADE[_vars]):
    v2:=setcont(ld,SADE[_vars]):
    vr:=setcont(v2,v1):
    vi:=v1 intersect v2:
    if vr<>v2 and vi<>v1 then
       nm:=cat(SADE[fname],SADE[fcount]):
       SADE[fcount]:=SADE[fcount]+1:
       if vi<>{} then
          nm:=nm(op(vi))
       fi:
       le:=le=nm:
       ld:=ld=nm:
       add_eqs:=add_eqs union {le,ld}:
       add_unks:=add_unks union {nm}
    else
       res:=res union {pr}
    fi
od:
res:=res union add_eqs:
res:=map(x->op(1,x)-op(2,x),res):
res:=map(x->numer(x),res):
[res,add_unks]
end:
# polydec
#
# Decomposes all equations which are polynomials in a variable
#
polydec:=proc()
local v,vd,i,j,eqs,p,res,flag:
global SADE:
eqs:=expand(SADE[_system][1] minus {0}):
v:=SADE[_vars]:
res:={}:
flag:=false:
for i from 1 to nops(eqs) do
    vd:={}:
    p:=eqs[i]:
    for j from 1 to nops(v) do
        if type(p,polynom(anything,v[j])) and degree(p,v[j])>0 then
           flag:=true:
           vd:=vd union {v[j]}
        fi
    od:
    p:=coeffs(p,[op(vd)]):
    res:=res union {p}:
    if SADE[traceout]=true and vd<>{} then
       print(``):
       print(`Decomposing the equation:`):
       print(eqs[i]):
       print(`as a polynomial expansion in the variables`):
       print(op(vd)):
       print(`and introducing the new equations`):
       print(p):
       print(``)
    fi:
od:
SADE[_system]:=[res,SADE[_system][2],SADE[_system][2]]:
flag
end:
# funcdecomp
#
# Applies first a polynomial decomposition in the variables. If not possible,
# tries all possible decompossitions as expansions in L.I. functions.
#
funcdecomp:=proc()
local f,fl:
f:=polydec():
fl:=f:
if not(f) then
   f:=decompfnc():
   fl:=f:
   while f do f:=decompfnc() od
fi:
fl
end:
# algsimp
#
# Searches in the global variable sistema for a purelly algebraic equation, determines its
# solutions and replaces it in SADE[_system].
#
algsimp:=proc()
local eqs,res,res2,i,j,k,s1,s2,prov,prov2,prov3,nmax,nn,inc,ns,_gh,npr,fl:
global SADE:
if nargs=1 then
   nmax:=args[1]
else
   nmax:=10^10
fi:
eqs:=expand(SADE[_system][1]):
if eqs={} then RETURN(false) fi:
ns:=nops(eqs):
inc:={op(map(x->op(0,x),SADE[incognita]))}:
for i from 1 to ns do
    res:=eqs[i]:
    nn:=traperror(timelimit(0.001,nops(res+_gh)-1)):
    fl:=false:
    if nn<>traperror then
       if nn<=nmax and not(has(res,diff)) and not(has(res,D)) then
          fl:=true
       fi
    fi:
    if fl then
       #res:=simplify(simpprod(prov)):
       prov:=[op(setcont(res,SADE[incognita]))]:
       npr:=nops(prov):
       prov:=convert(prov,array):
       for j from 1 to npr-1 do
           prov2:=prov[j]:
           if type(prov2,function) then
              prov3:=nops(prov2)
           else
              prov3:=0
           fi:
           for k from j+1 to npr do
               if nops(prov[k])>prov3 then
                  prov2:=prov[k]:
                  prov3:=nops(prov2)
               fi
           od:
           prov[j]:=prov2
       od:
       for j from 1 to npr do
           prov2:=solve(res,{prov[j]}):
           if {prov2}<>{} then
              s1:=setcont(op(1,prov2[1]),SADE[_vars]) minus inc:
              s2:=setcont(op(2,prov2[1]),SADE[_vars]) minus inc:
              if s2 minus s1={} and op(1,prov2[1])<>op(2,prov2[1]) then
                 if SADE[traceout]=true then
                    print(`Solving the algebraic equation:`):print(res):
                    print(`with solution:`):print(``):print(op(prov2)):print(``):
                 fi:
                 replace(prov2):
                 RETURN(true)
              fi
           fi
        od
    fi
od:
false
end:
# odesimp1
#
# Tries to solve a differential equation with a single term.
#
odesimp1:=proc()
local i,j,res,odeq,unk,prov,prov2,vd,vd2,varn,eqs,n,pvd:
global SADE:
eqs:=SADE[_system][1]:
for i from 1 to nops(eqs) do
    prov:=whichder2(eqs[i],SADE[incognita]):
    if nops(prov)=1 and has(prov,diff) then
    prov:=factor(op(i,eqs)):
    if type(prov,`*`) then
       j:=1:
       prov2:=1:
       while j<=nops(prov) do
             if setcont(op(j,prov),SADE[incognita])<>{} then
                prov2:=prov2*op(j,prov):
             fi:
             j:=j+1
       od:
       prov:=prov2
    fi:
    prov:=expand(prov):
    if has(prov,diff) and not(type(prov,`+`)) then
       vd:={}:
       if type(prov,`*`) then
          for j from 1 to nops(prov) do
              prov2:=op(j,prov):
              if has(prov2,diff) then
                 while has(prov2,diff) do
                       pvd:=op(2,prov2):
                       prov2:=op(1,prov2)
                 od:
                 unk:=prov2:
                 vd:=vd union {pvd}
              fi
          od
       else
          prov2:=prov:
          while has(prov2,diff) do
                pvd:=op(2,prov2):
                prov2:=op(1,prov2)
          od:
          unk:=prov2:
          vd:=vd union {pvd}:
       fi:
       if nops(unk)=1 then
          res:=dsolve(prov,unk):
          if {res}<>{} then
             SADE[incognita]:=SADE[incognita] minus {unk}:
             j:=1:
             while has(res,_C||j) or has(res,_F||j) do
                   varn:=cat(SADE[fname],SADE[fcount]):
                   res:=subs(_C||j=varn,_F||j=varn,res):
                   SADE[fcount]:=SADE[fcount]+1:
                   j:=j+1:
                   SADE[incognita]:=SADE[incognita] union {varn}
             od
          fi                  
       else
          res:=pdsolve(prov,unk):
          if nops(res)>1 and not(type(res,`=`)) then
             res:=op(1,res)
          fi:
          if {res}<>{} then
             SADE[incognita]:=SADE[incognita] minus {unk}:
             j:=1:
             while has(res,_F||j) do
                   varn:=cat(SADE[fname],SADE[fcount]):
                   SADE[incognita]:=SADE[incognita] union {subs(_F||j=varn,searchfunction(res,_F||j))}:
                   res:=subs(_F||j=varn,res):
                   SADE[fcount]:=SADE[fcount]+1:
                   j:=j+1
             od
          fi
       fi:
       #paramcond_add(eqs[i]):
       if SADE[traceout]=true and {res}<>{} then
          print(``):
          print(`Solving the differential equation:`):
          print(eqs[i]):
          print(`with solution:`):print(res):print(``)
       fi:
       replace(res):
       #SADE[_system]:=subs(res,SADE[_system]):
       RETURN(true)
    fi
    fi
od:
false
end:
# decompfnc
#
# Looks for each equation in the global variable SADE[_system] for a decomposition in linearly independent functions.
# If called with argument 2 then if first replaces each equation by its numerator in the normal form 
#
decompfnc:=proc()
local i,j,k,res,eqs,prov,flag,fncs,p1,p2,e2,und,id,adsub,eqdc:
global SADE:
und:=proc(x) 1 end:
id:=proc(x) x end:
SADE[incognita]:=simplify(SADE[incognita]):
SADE[_system][1]:=combine(map(x->numer(x),SADE[_system][1]),trig):
eqs:=[op(expand(SADE[_system][1]) minus {0})]:
if nargs=1 and args[1]=2 then
   eqs:=simplify(map(x->numer(x),eqs))
fi:
flag:=false:
for i from 1 to nops(SADE[_vars]) do
    res:={}:
    for j from 1 to nops(eqs) do
        eqdc:=simpprod(eqs[j]):
        #prov:=traperror(lifdec(eqs[j],op(i,SADE[_vars]))):
        prov:=traperror(lifdec(eqdc,op(i,SADE[_vars]))):
        if prov=lasterror then
           prov:=eqdc:
           if prov<>0 then
              prov:=traperror(lifdec(prov,op(i,SADE[_vars]))):
              if prov=lasterror then
                 prov:=[{eqdc},{}]
              fi
           else
              prov:=[{eqdc},{}]
           fi
        fi:
        if nops(prov)=3 then
           adsub:=prov[3]
        else
           adsub:={}
        fi:
        fncs:=prov[2]:
        prov:=prov[1] minus {0}:
        #if prov<>{} and not(has(eqs,prov[1])) then
        if prov<>{} and fncs<>{} then
           prov:=eval(subs(adsub,prov)):
           prov:=simplify(map(x->numer(x),prov),symbolic) minus {0}:
           prov:=eval(subs(abs=id,prov)):
           prov:=eval(subs(csgn=id,prov)):
           if prov<>{} and nops(prov)>1 then
              flag:=true:
              if SADE[traceout]=true then
                 if adsub<>{} and SADE[traceout]=true then
                    print(``):
                    print(`Replacing the linearly dependent functions:`):
                    print(adsub)
                 fi:
                 print(`Decomposing the equation:`):
                 print(eqdc):
                 print(`as an expansion in the set of L.I. functions:`):
                 print({op(fncs)}):
                 print(`and introducing the new equation(s):`):
                 print(``):print(op(prov)):print(``)
              fi
           fi:
           #eqs[j]:=0:
           res:=res union prov
        else
           if (nops(prov)=2 and type(prov,list)) or prov={} then
              if prov<>{} then
                 res:=res union {prov[1]}
              fi
           else
              res:=res union {eqdc}
           fi
        fi
    od:
    eqs:=[op(res)]
od:
eqs:={op(eqs)} minus {0}:
SADE[_system]:=[eqs,SADE[_system][2],SADE[_system][3]]:
flag
end:
# singlediffsolve
#
# Solves all single term differential equations
#
singlediffsolve:=proc()
local i,j1,j2,kk,qq1,qq2,r,syst,unks,eqs1,eqs2,p,p2,inv,vd,vnm,ff,_gh,nn:
global SADE:
syst:=expand(SADE[_system][1]) minus {0}:
unks:=SADE[incognita]:
kk:=nops(syst):
qq1:=array(1..kk):
qq2:=array(1..kk):
j1:=1:
j2:=1:
for i from 1 to kk do
    p:=syst[i]:
    p2:=traperror(timelimit(0.001,nops(p+_gh)-1)):
    if p2<>lasterror and p2=1 and setcont(whichder(p),unks)<>{} then
       qq1[j1]:=p:
       j1:=j1+1
    else
       qq2[j2]:=p:
       j2:=j2+1
    fi
od:
j1:=j1-1:
j2:=j2-1:
eqs1:=convert(qq1,set) minus {0}:
eqs2:=convert(qq2,set) minus {0}:
if j1>0 then
   eqs1:=eqs1[1..j1]
fi:
if j2>0 then
   eqs2:=eqs2[1..j2]
fi:
############################################
if eqs1={} then
   RETURN(false):
fi:
p:=setcont(eqs1,unks):
r:=singlesolve(eqs1,p):
i:=1:
while has(r,cat(_C,i)) do
      vnm:=cat(SADE[fname],SADE[fcount]):
      r:=subs(cat(_C,i)=vnm,r):
      i:=i+1:
      SADE[fcount]:=SADE[fcount]+1:
      SADE[incognita]:=SADE[incognita] union {vnm}
od:
vd:={}:
ff:=whichfunction(r) minus SADE[incognita]:
for i from 1 to nops(ff) do
      vnm:=cat(SADE[fname],SADE[fcount]):
      r:=subs(op(0,ff[i])=vnm,r):
      p:=subs(op(0,ff[i])=vnm,ff[i]):
      vd:=vd union {p}:
      SADE[fcount]:=SADE[fcount]+1:
      SADE[incognita]:=SADE[incognita] union {p}
od:
if SADE[traceout]=true then
   print():
   print(`Solving the single term equation(s):`):
   print():
   for i from 1 to nops(eqs1) do
       print(eqs1[i]):print()
   od:
   print():
   print(`with solution(s):`):
   print():
   for i from 1 to nops(r) do
       print(r[i]):print()
   od:
   print():
fi:
eqs2:=subs(r,eqs2):
p:=map(x->op(1,x),r):
SADE[incognita]:=SADE[incognita] minus p union vd:
SADE[_system]:=[eqs2,subs(r,SADE[_system][2]),SADE[_system][2]]:
true
end:
# singlesolve
#
# Solves a set in eqs_in of single term differential equations in the
# unknowns in unks.
#
singlesolve:=proc(eqs_in,unks)
local i,j,countc,countf,sincog,neweq,nm,mm,sglunk,res,r2,peq,pos,pr,wf,prsol:
countc:=0:
countf:=0:
sincog:=[op(unks)]:
r2:=eqs_in:
mm:=nops(sincog):
neweq:=array(1..mm):
for i from 1 to mm do
    neweq[i]:={}
od:
for i from 1 to nops(r2) do
    peq:=setcont(r2[i],sincog):
    pos:=posvars(peq[1],sincog):
    neweq[pos]:=neweq[pos] union {r2[i]}
od:
for i from 1 to mm do
    pr:=neweq[i]:
    if pr<>{} then
       pr:=clean_eqs(pr,sincog):
       sglunk:=setcont(pr,sincog):
########################
       prsol:=traperror(pdsolve(pr,sglunk)):
########################
       if prsol=lasterror then
          prsol:=dsolve(pr,sglunk)
       fi:
       neweq[i]:=prsol
    fi
od:
res:={}:
sincog:={op(sincog)}:
for i from 1 to mm do
    pr:=neweq[i]:
    if pr<>{} then
       wf:=whichfunction(pr) minus sincog:
       for j from 1 to nops(wf) do
           countf:=countf+1:
           nm:=cat(_f,countf):
           pr:=subs(op(0,wf[j])=nm,pr)
       od:
       j:=1:
       while has(pr,cat(_C,j)) do
             countc:=countc+1:
             nm:=cat(_cc,countc):
             pr:=subs(cat(_C,j)=nm,pr):
             j:=j+1
       od:
       if type(pr,set) then
          res:=res union pr
       else
          res:=res union {pr}
       fi
    fi
od:
for i from 1 to countf do
    res:=subs(cat(_f,i)=cat(_F,i),res)
od:
for i from 1 to countc do
    res:=subs(cat(_cc,i)=cat(_C,i),res)
od:
res
end:
# diffsolve
#
# Solves an ordinary differential or algebraic equation in one of the unknowns.
# If the argument is 1 is uses odesimpv1. In case of no argument it uses odesimpv.
# If the argument is 2 then it solves only purelly differential equations uisng odesimpv.
#
diffsolve:=proc()
local i,j,n,eqs,fd,prov,prov2,prov3,vr,flag,flag2,nome,addeq,addeq2,v,v1,v2,nrg,sol,sol2,k,md,md2,pr:
global SADE:
if SADE[_system][1]={} then RETURN(false) fi:
if nargs>=1 then
   nrg:=nargs
else
   nrg:=0
fi:
SADE[_system]:=[convert(SADE[_system][1],diff),SADE[_system][2],SADE[_system][3]]:
#eqs:=eval(sizeorder(op(1,SADE[_system]))):
eqs:=SADE[_system][1]:
fd:={}:
for i from 1 to nops(SADE[incognita]) do
    if type(SADE[incognita][i],function) then
       fd:=fd union {SADE[incognita][i]}
    fi
od:
i:=1:
prov:=false:
while i<=nops(eqs) and prov=false do
#    prov2:=expand(simpprod(eqs[i])):
    prov2:=expand(eqs[i]):
    if type(SADE[_freefunctions],set) and setcont(prov2,SADE[_freefunctions])<>{} then
       prov:=false
    else
       if type(prov2,`+`) then
          prov:=false:
          if nrg=1 then
             if args[1]>=nops(prov2) and args[1]>1 then
                prov:=traperror(odesimpv(prov2,fd)):
             fi
          else
             prov:=traperror(odesimpv(prov2,fd))
          fi:
       fi
    fi:
    if type(prov[2],set) and prov[2]<>{} then
       prov:=false
    fi:
    if prov=lasterror then
       prov:=false
    else
       if prov<>false then
          if type(prov[1],list) then
             pr:=prov[1][1]
          else
             pr:=prov[1]
          fi:
          #pr:=combine(pr,trig):
          #pr:=simplify(pr,symbolic):
          v1:=setcont(op(1,pr),SADE[_vars]):
          v2:=setcont(op(2,pr),SADE[_vars]):
          if v2 minus v1<>{} then
             prov:=false
          fi
       fi
    fi:
    if has(prov,int) or has (prov,Int) then prov:=false fi:
    if nrg=1 and args[1]>1 and not(has(prov,_C1)) and not(has(prov,_F1)) then
       prov:=false
    fi:
    prov:=eval(prov):
    if prov<>false then
       if type(prov[1],list) then
#########################################################
          #addeq:=prov[2]:
          addeq:={op(2,prov[1][1])}:
#########################################################
          prov:=prov[1]
       else
          addeq:={}
       fi:
       if setcont(op(2,prov[1]),SADE[_vars]) minus setcont(op(1,prov[1]),SADE[_vars])<>{} and addeq={} then
          prov:=false
       else
          prov2:=var_int(prov):
          if prov2<>{} then
             prov:=false
          fi
       fi
    fi:
    i:=i+1
od:
n:=i-1:
if prov<>false then
   i:=1:
   flag:=false:
   vr:=prov[2]:
   if not(type(vr,set)) then vr:={vr} fi:
   prov:=prov[1]:
   while has(prov,_C||i) or has(prov,_F||i) do
         flag:=true:
         nome:=cat(SADE[fname],SADE[fcount]):######################################
         if has(prov,_C||i) then
            prov:=subs(_C||i=nome,prov):
            addeq:=subs(_C||i=nome,addeq):
            SADE[incognita]:=SADE[incognita] union {nome}:
            SADE[fcount]:=SADE[fcount]+1
         fi:
         nome:=cat(SADE[fname],SADE[fcount]):
         if has(prov,_F||i) then
            prov:=subs(_F||i=nome,prov):
            addeq:=subs(_F||i=nome,addeq):
            prov2:={op(op(1,prov))} minus vr:
            prov2:=op(prov2):
            SADE[incognita]:=SADE[incognita] union {nome(prov2)}:
            SADE[fcount]:=SADE[fcount]+1
         fi:
         if type(op(1,prov),`=`) then prov:=op(1,prov) fi:
         SADE[incognita]:=SADE[incognita] minus {prov[1]}:
         prov2:={op(op(1,prov))} minus vr:
         prov2:=op(prov2):
         #if {prov2}={} then
         #   SADE[incognita]:=SADE[incognita] union {nome}
         #else
         #   SADE[incognita]:=SADE[incognita] union
         #           {nome(prov2)}:
         #   if has(prov,_C||i) and {prov2}<>{} then
         #      prov:=subs(nome=nome(prov2),prov):
         #      addeq:=subs(nome=nome(prov2),addeq)
         #   else
               if {prov2}<>{} then
                  prov3:=searchfunction(op(2,prov),nome):
                  prov:=subs(prov3=nome(prov2),prov):
                  addeq:=subs(prov3=nome(prov2),addeq)
               fi:
         #   fi:
         #fi:
         i:=i+1
   od:
   addeq2:={}:
   flag2:=true:
   if type(prov,set) or type(prov,list) then
      prov3:=prov[1]
   else
      prov3:=prov
   fi:
   v1:=setcont(op(1,prov3),SADE[_vars]):
   v2:=setcont(op(2,prov3),SADE[_vars]):
   v:=v2 intersect v1:
   if v<>v2 then
      prov2:=traperror(rifsimp({eqs[n]},[op(setcont(eqs[n],SADE[incognita]))])):
      if prov2=lasterror then
         if prov2="system is inconsistent" then
            ERROR(res)
         fi:
         nome:=cat(SADE[fname],SADE[fcount]):
         addeq:=op(2,prov3):
         if not(type(SADE[forbiden],set)) then SADE[forbiden]:={} fi:
         if v={} then
            addeq2:=addeq2 union {addeq-nome}:
            SADE[incognita]:=SADE[incognita] union {nome}:
            SADE[forbiden]:=SADE[forbiden] union {nome}
         else
            addeq2:=addeq2 union {addeq-nome(op(v))}:
            SADE[incognita]:=SADE[incognita] union {nome(op(v))}:
            SADE[forbiden]:=SADE[forbiden] union {nome(op(v))}
         fi:
         SADE[fcount]:=SADE[fcount]+1
      else
         flag2:=false:
         prov2:=map(x->op(1,x)-op(2,x),{op(prov2[Solved])})
      fi
   fi:
   if flag2 then
      SADE[_system]:=[SADE[_system][1] union addeq2,SADE[_system][2],SADE[_system][3]]:
      if SADE[traceout]=true then
         print(``):
         if flag then
            print(`Solving the ordinary differential equation:`)
         else
            print(`Solving the algebraic equation:`)
         fi:
         print(eqs[n]):
         print(`with solution:`):print(prov):print(``):
         if addeq2<>{} then
            print(`and introducing the compatibility equation(s):`):
            print(op(addeq2)):print(``)
         fi
      fi:
      replace(prov)
   else
      sol2:=traperror(pppdsolve(prov2,setcont(prov2,SADE[incognita]))):
      if sol2=lasterror or has(sol2,PDESolStruc) then
         RETURN(false)
      fi:
      sol:={}:
      for i from 1 to nops(sol2) do
          if not(has(sol2[i],Int) or has(sol2[i],int)) then
             sol:=sol union {sol2[i]}
          fi
      od:
###############################################
      if sol<>{} and type(sol[1],set) then
         sol:=map(x->op(x),sol)
      fi:
###############################################
      sol:=tautoelim(sol):
      if sol={} then RETURN(false) fi:
      for i from 1 to nops(sol) do
          v1:=setcont(op(1,sol[i]),SADE[_vars]):
          v2:=setcont(op(2,sol[i]),SADE[_vars]):
          v:=v2 minus v1:
          if v<>{} then
             for j from 1 to nops(v) do
                prov2:=lifdec(eqs[n],v[j]):
                if prov2[2]<>{} then
                   SADE[_system]:=[{op(eqs)} minus {eqs[n]} union
                                   prov2[1],SADE[_system][2],SADE[_system][3]]:
                   if SADE[traceout]=true then
                      print(``):
                      print(`Decomposing the single equation`):
                      print(eqs[n]):
                      print(`as an expansion in the L.I. functions`):
                      print(prov2[2]):
                      print(`and introducing the new equations`):
                      print(op(prov2[1])):
                      print(``)
                   fi:
                   RETURN(true)
                fi:
                RETURN(false)
             od
          fi
      od:
      k:=0:
      md:=setcont(sol,SADE[incognita]):
      md2:=whichder(prov2):
      for i from 1 to nops(md) do
          k:=k+derdeg(md2,md[i])
      od:
      for i from 1 to 3*k do
          if has(sol,cat(_F,i)) then
             nome:=cat(SADE[fname],SADE[fcount]):
             md:=op(searchfunction(sol,cat(_F,i))):
             sol:=subs(cat(_F,i)=nome,sol):
             SADE[incognita]:=SADE[incognita] union {nome(md)}:
             SADE[fcount]:=SADE[fcount]+1
          fi
      od:
      i:=1:
      while has(sol,cat(_C,i)) do
            nome:=cat(SADE[fname],SADE[fcount]):
            sol:=subs(cat(_C,i)=nome,sol):
            SADE[incognita]:=SADE[incognita] union {nome}:
            SADE[fcount]:=SADE[fcount]+1:
            i:=i+1
      od:
      if SADE[traceout]=true then
         print(``):
         print(`Rearranging the differential equation:`):
         print(eqs[n]):
         print(`into the equivalent form:`):print(``):
         print(op(prov2)):print(``):
         print(`with solution:`):print(``):
         print(sol):print(``)
      fi:
      replace(sol)
   fi
else
   prov:=false
fi:
if prov<>false then
   prov:=true
fi:
SADE[_system]:=eval(subs(Int=iint,SADE[_system])):
prov
end:
# pdiffsolve
# Solve a partial differential equation provided it passes the test by isitinteg.
# Synopsis
# result:=pdiffsolve()
# Parameters
# result: a boolean value (true or false).
# Description
# Solve a partial differential equation provided it passes the test by isitinteg.
# Code
pdiffsolve:=proc()
local i,i2,j,k,res,prov,prov2,eqs,_gh:
global SADE:
eqs:=op(1,SADE[_system]) minus {0}:
eqs:=sizeorder(eqs):
if eqs={} then RETURN(false) fi:
for i from 1 to nops(eqs) do
    res:=traperror(pdsolve(eqs[i])):
    if lasterror<>res and {res}<>{} and not(has(res,int)) and not(has(res,Int)) and not(has(res,_a))
       and not(has(res,`&where`)) and op(0,res)<>PDESolStruc then
       res:=eval(res):
       k:=1:
# Here the solution of pdsolve must be regularizes due to a bug in the
# maple routine, which returns different arbitrary functions with the same
# name. It also verifies if the obtained solution has the correct number of
# arbitrary functions.
       prov:=op(2,res):
       i2:=1:
       j:=1:
       while has(prov,cat(_F,i2)) do
             prov2:=searchfunction(prov,cat(_F,i2)):
             prov:=eval(subs(prov2=cat(_gh,j)(op(prov2)),prov)):
             j:=j+1:
             if not(has(prov,cat(_F,i2))) then
                i2:=i2+1
             fi
       od:
       for i2 from 1 to j-1 do
           prov:=eval(subs(cat(_gh,i2)=cat(_F,i2),prov))
       od:
#
       if derdeg(eqs[i],op(1,res))=j-1 then
          prov:=_F1:
          while has(res,prov) do
                prov2:=cat(SADE[fname],SADE[fcount]):
                SADE[fcount]:=SADE[fcount]+1:
                res:=subs(prov=prov2,res):
                prov2:=searchfunction(res,prov2):
                SADE[incognita]:=SADE[incognita] union {prov2}:
                k:=k+1:
                prov:=cat(_F,k)
          od:
          k:=1:
          prov:=_C1:
          while has(res,prov) do
                prov2:=cat(SADE[fname],SADE[fcount]):
                SADE[fcount]:=SADE[fcount]+1:
                res:=subs(prov=prov2,res):
                SADE[incognita]:=SADE[incognita] union {prov2}:
                k:=k+1:
                prov:=cat(_F,k)
          od:
          if SADE[traceout]=true then
             print(``):print(`Solving the partial differential equation:`):print(eqs[i]):
             print(`with solution`):print(res):print(``)
          fi:
          SADE[_system]:=convert(SADE[_system],diff):
          replace(res):
          #SADE[_system]:=simplify(subs(res,SADE[_system])):
          #SADE[incognita]:=SADE[incognita] minus {op(1,res)}:
          RETURN(true)
       fi
    fi
od:
if nargs=1 and args[1]=2 then
   eqs:=SADE[_system][1]:
   prov:=SADE[incognita]:
   prov2:={}:
   for i from 1 to nops(prov) do
       if has(eqs,prov[i]) then
          prov2:=prov2 union {prov[i]}
       fi
   od:
   res:=pdsolve(eqs,prov2):
   k:=1:
   prov:=_F1:
   while has(res,prov) do
         prov2:=cat(SADE[fname],SADE[fcount]):
         SADE[fcount]:=SADE[fcount]+1:
         res:=subs(prov=prov2,res):
         prov2:=searchfunction(res,prov2):
         SADE[incognita]:=SADE[incognita] union {prov2}:
         k:=k+1:
         prov:=cat(_F,k):
   od:
   k:=1:
   prov:=_C1:
   while has(res,prov) do
         prov2:=cat(SADE[fname],SADE[fcount]):
         SADE[fcount]:=SADE[fcount]+1:
         res:=subs(prov=prov2,res):
         SADE[incognita]:=SADE[incognita] union {prov2}:
         k:=k+1:
         prov:=cat(_F,k)
   od:
   #paramcond_add(eqs[i]):
   if SADE[traceout]=true then
      print(``):print(`Solving the partial differential equation(s):`):print(eqs):
      print(`with solution`):print(res):print(``)
   fi:
   SADE[_system]:=convert(SADE[_system],diff):
   replace(res):
   #SADE[_system]:=subs(res,SADE[_system]):
   #SADE[incognita]:=SADE[incognita] minus {op(1,res)}:
   RETURN(true)
fi:
false
end:
# odesimpv
#
# Solves a given ordinary differential equation in one of the unknowns.
#
odesimpv:=proc()
local i,j,k,vv,ff,flag,algflag,dv,prov,prov2,prov3,eq,fd,res,pres,v1,v2,addeq,um:
global SADE,_gh,_gh2:
options remember:
um:=proc(x) 1 end:
eq:=simplify(args[1]):
eq:=combine(eq,trig):
fd:=setcont(args[2],SADE[incognita]):
prov:=isitinteg(eq):
if prov=false then RETURN(false) fi:
fd:=fd intersect prov:
res:={}:
for i from 1 to nops(fd) do
    ff:=fd[i]:
    flag:=false:
    algflag:=false:
    if has(eq,ff) then
       vv:=[op(ff)]:
       flag:=true:
       dv:={}:
       prov:=expand(eq)+_gh:
       for j from 1 to nops(prov) do
           prov2:=op(j,prov)*_gh2:
           for k from 1 to nops(prov2) do
               prov3:=op(k,prov2):
               if has(prov3,diff) and has(prov3,ff) then
                  while op(0,prov3)<>diff do
                        prov3:=op(1,prov3)
                  od:
                  while op(0,prov3)=diff do
                    dv:=dv union {op(2,prov3)}:
                    prov3:=op(1,prov3)
                  od
               fi
           od
       od:
       if nops(dv)=1 and nargs=2 then
          dv:=dv[1]:
          j:=1:
          if flag then
             pres:={}:
             #if nops(ff)=1 and setcont(eq,SADE[_vars]) intersect {op(ff)}=setcont(eq,SADE[_vars]) then
             if nops(ff)=1 then
# Aqui introduzi traperror para contornar um bug em dsolve.
                prov:=traperror(dsolve(eq,ff)):
                if {prov}<>{} and prov<>lasterror and type(prov,`=`) then
                   prov:=expand(prov):
                   pres:={[prov,dv]}
                fi
             else
                prov:=traperror(pdsolve(eq,ff)):
                if prov<>lasterror and type(prov,`=`) and type(prov,set) then
                   prov:=expand(prov):
                   prov:=op(1,prov)
                fi:
                if prov<>lasterror and type(prov,`=`) then
                   pres:={[prov,dv]}
                fi
             fi:
             pres:=intsimp(pres):
             res:=res union pres
          fi
       fi:
       if dv={} then
          prov:={solve(eq,{ff})}:
          for j from 1 to nops(prov) do
              res:=res union {[op(prov[j]),dv]}
          od:
          algflag:=true
       fi:
    fi
od:
if res={} then
   RETURN(false)
fi:
for i from 1 to nops(res) do
###############################################################################################
    prov:=eval(subs(signum=um,csgn=um,res[i])):
    prov:=simplify(symbolic):
###############################################################################################
    if not(has(prov,I)) and ((var_int(prov[1])={} and (has(prov[1],_C1) or has(prov[1],_F1))) or algflag) then
       v1:=setcont(op(1,prov[1]),SADE[_vars]):
       v2:=setcont(op(2,prov[1]),SADE[_vars]):
       #if not(has(op(1,prov[1]),SADE[forbiden])) or algflag then
          if v2 minus v1={} then
             RETURN(prov)
          else
             addeq:=varcompat(prov[1]):
             if addeq<>false then
                RETURN([prov,addeq])
             fi
          fi
       #fi
    fi
od:
for i from 1 to nops(res) do
    prov:=res[i]:
    if not(has(prov,I)) and ((var_int(prov[1])={} and not(has(op(1,prov[1]),SADE[forbiden]))) or algflag) then
       v1:=setcont(op(1,prov[1]),SADE[_vars]):
       v2:=setcont(op(2,prov[1]),SADE[_vars]):
       if v2 minus v1={} then
          RETURN(prov):
       fi
    fi
od:
false
end:
# algsimpdiff
# Tries to solve one algebraic equation even if the remaining terms contain derivatives.
# Synopsis
# result:=algsimpdiff
# Parameters
# result: a boolena value (true or false).
# Description
# Tries to solve one algebraic equation even if theremaining terms contain derivatives.
# Code
algsimpdiff:=proc()
local res,i,j,k,ff,eqs,res2,res3,flag,prov,prov2,prov3,prov4:
global SADE:
if nargs=1 and setcont(SADE[incognita],SADE[_unks0])={} then
   RETURN(false)
fi:
eqs:=expand(map(x->numer(x),expand(SADE[_system][1]))):
if eqs minus {0}={} then RETURN(false) fi:
#eqs:=sizeorder(eqs):
i:=1:
flag:=true:
while i<=nops(eqs) and flag do
      res:={}:
      prov:=whichder(eqs[i]):
      if nargs=1 then
         prov:=setcont(prov,args[1]):
         prov2:=setcont(eqs[i],args[1])
      else
         prov:=setcont(prov,SADE[incognita]):
         prov2:=setcont(eqs[i],SADE[incognita])
      fi:
      ff:=prov2 minus prov:
      ff:=morevars(ff):
      if ff<>{} then
         res:={eqs[i]}:
      fi:
      i:=i+1:
      if res<>{} then
         res:=eval(tautoelim(solve(res,ff))):
         if res<>{} and setcont(op(1,res[1]),setcont(op(2,res[1]),SADE[_vars]))=
            setcont(op(2,res[1]),SADE[_vars]) then
            flag:=false
         fi
      fi
od:
eqs:=eqs[i-1]:
if res={} or flag then
   RETURN(false)
fi:
prov:={}:
res2:={}:
for i from 1 to nops(res) do
    if op(1,res[i])<>op(2,res[i]) then
       SADE[incognita]:=SADE[incognita] minus {op(1,res[i])}:
       res2:=res2 union {expand(res[i])}#############
    fi
od:
if SADE[traceout]=true then
   print(`Solving the algebraic equation(s):`):print(eqs):
   print(`with solution(s):`):print(``):print(op(res2)):print(``):
fi:
replace(res2):
#SADE[_system]:=subs(res2,SADE[_system]):
#SADE[_system][1]:=SADE[_system][1] minus {0}:
true
end:
# morevars
morevars:=proc(funcs)
local i,p,p2,res,v,t1,t2:
global SADE:
if funcs={} then
   RETURN({})
fi:
v:=SADE[_vars]:
p:=setcont(funcs[1],v):
res:={funcs[1]}:
for i from 2 to nops(funcs) do
    p2:=setcont(funcs[i],v):
    if p2=p then
       res:=res union {funcs[i]}
    else
       t1:=p minus p2:
       t2:=p2 minus p:
       if t2<>{} and t1={} then
          p:=p2:
          res:={funcs[i]}
       fi 
    fi
od:
res
end:
# varcompat
#
# Looks both sides of an equation for compatibility in the variables and introduces new equations if needed.
# Returns a set of expressions that must be equated to functions of the variables on the left-hand side
# minus the derivative variables.
#
varcompat:=proc(sol)
local i,j,res,fncs,v1,v2,vint,lhs,rhs,addeq,prov,oldeqs,flag,n:
global SADE:
#print(`sol=`,sol):
lhs:=op(1,sol):
rhs:=op(2,sol):
v1:=setcont(lhs,SADE[_vars]):
v2:=setcont(rhs,SADE[_vars]):
vint:=v2 intersect v1:#print(v1,v2,vint):
if v2 minus v1={} then RETURN({}) fi:
addeq:={expand(rhs)}:
oldeqs:=addeq:
for i from 1 to nops(vint) do
    res:={}:
    for j from 1 to nops(addeq) do
        prov:=lifdec(addeq[j],vint[i]):
        fncs:=prov[2]:#print(`decomposicao`,i,prov,fncs,vint[i]):
        n:=1:
        flag:=true:
        while flag and has(sol,_F||n) do
              if has(fncs,_F||n) then
                 flag:=false:#print(flag):
              fi:
              n:=n+1
        od:
        prov:=prov[1] minus {0}:
        if flag then
           res:=res union prov
        fi
    od:
    addeq:=res
od:
if setcont(addeq,SADE[_vars])=v2 then
   RETURN(false)
fi:#print(`addeq=`,addeq):
addeq
end:
# sizeorder
#
# Orders a set of equations in ascending size.
#
sizeorder:=proc(eqs)
local i,j,eqs2,n,tamanho,m1,m2,mtr,eqtr,eqs3,k,menor,nm:
eqs2:={op(expand(eqs))} minus {0}:
n:=nops(eqs2):
eqs2:=convert([op(eqs2)],Array):
for i from 1 to n do
    tamanho[i]:=nops(eqs2[i]+_gh)-1:
od:
for i from 1 to n-1 do
    m1:=tamanho[i]:
    menor:=m1:
    nm:=i:
    for j from i+1 to n do
        m2:=tamanho[j]:
        if m2<menor then
           menor:=m2:
           nm:=j
        fi
    od:
    eqtr:=eqs2[nm]:
    eqs2[nm]:=eqs2[i]:
    eqs2[i]:=eqtr:
    mtr:=tamanho[nm]:
    tamanho[nm]:=tamanho[i]:
    tamanho[i]:=mtr:
od:
eqs3:=seq(eqs2[k],k=1..n):
[eqs3]
end:
# searchfunction
#
# Searches fo a given function in a MAPLE expression and returns the function with its argument.
#
# OLD VERSION:
#
#searchfunction:=proc(a,f)
#local i,ex,prov:
#ex:=expand(a):
#if a=f then RETURN(a) fi:
#for i from 1 to nops(ex) do
#    prov:=op(i,ex):
#    if has(prov,f) then
#       if type(prov,function) and not(type(op(1,prov),function)) then
#          RETURN(prov)
#       else
#          RETURN(searchfunction(prov,f))
#       fi
#    fi
#od:
#false
#end:
searchfunction:=proc(a,f)
local i,ex,prov,b,ghost:
b:=f:
if type(b,function) then
   b:=op(0,b)
fi:
if not(has(a,b)) then
   RETURN(false)
fi:
ex:=expand(a):
if a=f then RETURN(a) fi:
for i from 1 to nops(ex) do
    prov:=op(i,ex):
    if has(prov,f) then
       if type(prov,function) and not(type(op(1,prov),function)) then
          if op(0,prov)=b then
             RETURN(prov)
          else
             prov:={op(prov)}:
             prov:=map(x->searchfunction(x,f),prov) minus {false}:
             if prov={false} then
                RETURN(false)
             else
                RETURN(prov[1])
             fi
          fi
       else
          RETURN(searchfunction(prov,b))
       fi
    fi
od:
false
end:
# var_int
# Determines which functions in SADE[incognita] are integrated in the argument.
# Synopsis
# result:=var_int(a)
# Parameters
# result: a set.
# a: a maple expression.
# Description
# Determines which fucntions in the global variable incognita are integrated in the argument.
# Code
var_int:=proc(a)
local i,res,prov,aa,termo:
global SADE,_gh,___isres:
___isres:={}:
eval(subs(int=int_subs,a)):
eval(subs(Int=int_subs,a)):
___isres
end:
# int_subs
# Used by var_int to determine which functios are integrated ina given expression.
# Synopsis
# result:=int_subs(a,b)
# Parameters
# result: a Maple expression.
# a: a Maple expression.
# b: a variable name.
# Description
# Used by var_int to determine which functios are integrated ina given expression.
# Code
int_subs:=proc(a,b)
local res,res2,i:
global ___isres:
res2:=setcont(a,SADE[incognita]):
res:={}:
for i from 1 to nops(res2) do
    if has(res2[i],b) then
       res:=res union {res2[i]}
    fi
od:
___isres:=___isres union res:
_iint(a,b)
end:
# lifdec
#
# Returns the coefficients of a set of linearly independent functions of an expression in b,
# with respect to the variable y.
# if not possible it returns the list of found functions.
#
lifdec:=proc(b,y)
local a,c,prov,fnclist,i,v,p,res:
global SADE,_gh:
options remember:
if type(y,set) then
   res:={}:
   for i from 1 to nops(y) do
       res:=res union {lifdec(b,y[i])}
   od:
   RETURN(res)
fi:
c:=expand(b):
if type(c,`*`) then
   a:=1:
   for i from 1 to nops(c) do
       if setcont(op(i,c),SADE[incognita])<>{} then
          a:=a*op(i,c)
       fi
   od
else
   a:=c
fi:
if a=1 then RETURN([{a},{}]) fi:
fnclist:=orderfunctions([op(lifunc(a,y))]):
if {fnclist}={} then
   RETURN([{a},{}]):
fi:
if fnclist<>[] then
   if SADE[_nolifdecindep]<>true then
      p:=funcrellin(fnclist,y)
   else
      p:=false
   fi:
   if p=lasterror then
      p:=false
   fi:
   if p<>false then
      a:=expand(subs(p,a))
   fi
fi:
if has(fnclist,diff) or fnclist={} or has(fnclist,D) or
          setcont(fnclist,SADE[incognita])<>{} or fnclist={} or
          setcont(fnclist,SADE[_decompvar])={} then
   RETURN([{a},{}])
fi:
SADE[_lasteq]:=a:
v:={}:
prov:={}:
for i from 1 to nops(fnclist) do
    a:=eval(rpsub(fnclist[i],_gh,a)):
    prov:=prov union {coeff(a,_gh,1)}:
    a:=coeff(a,_gh,0):
od:
prov:=prov union {a}:
if (setcont(prov,SADE[_vars]) intersect setcont(op(1,fnclist),SADE[_vars]))<>{} then
   prov={}
fi:
prov:=prov minus {0}:
if p=false then
   res:=[prov,fnclist]
else
   res:=[prov,fnclist,p]
fi:
res
end:
# funcrellin
#
# Verifies if functions in f in variable x, plus the unit function, are linearly dependent.
# If not, returns false. In the other case, returns the substitution rules with the linearly
# dependent functions as an expansion of the linearly independent.
#
funcrellin:=proc(f,x)
local w,f2,p,r,_v,n,i,j,k,vr,rvc,s,res:
f2:=[op(f),1]:
n:=nops(f2):
w:=VectorCalculus[Wronskian](f2,x):
p:=simplify(LinearAlgebra[Determinant](w)):
if p<>0 then RETURN(false) fi:
w:=convert(w,Matrix):
r:={}:
vr:={}:
for i from 1 to n do
    p:=0:
    vr:=vr union {cat(_v,i)}:
    for j from 1 to n do
        p:=p+cat(_v,j)*w[i,j]
    od:
    r:=r union {p}
od:
r:=simplify(simplify(r,symbolic),trig):
r:=solve(r,vr):
rvc:=[seq(cat(_v,i),i=1..n)]:
rvc:=subs(r,rvc):
vr:=setcont(rvc,vr):
s:={}:
for i from 1 to nops(vr) do
    p:=rvc:
    for j from 1 to nops(vr) do
        if i=j then
           p:=subs(vr[i]=1,p)
        else
           p:=subs(vr[j]=0,p)
        fi:
    od:
    s:=s union {p}
od:
res:={}:
for i from 1 to nops(s) do
    k:=1:
    while s[i][k]=0 do
          k:=k+1
    od:
    p:=s[i][k]:
    r:=0:
    for j from k+1 to n do
        r:=r-s[i][j]*f2[j]/p
    od:
    res:=res union {f2[k]=r}
od:
res
end:
# lifunc
#
# Returns a list with the functions in the variable y that
# are present in a.
#
lifunc:=proc(a,y)
local i,j,prov,prov2,res,func:
global SADE,_gh:
prov:=expand(a):
if not(type(prov,`+`)) then prov:=prov+_gh fi:
res:={}:
for i from 1 to nops(prov) do
        prov2:=op(i,prov):
        if has(prov2,y) then
                if type(prov2,`*`) then
                        func:=1:
                        for j from 1 to nops(prov2) do
                                if has(op(j,prov2),y) then
                                        func:=func*op(j,prov2):
                                fi:
                                res:=res union {func}
                        od
                else
                        res:=res union {prov2}
                fi
        fi:
od:
res:=res minus {1}:
if setcont(res,SADE[incognita])<>{} then
   RETURN({})
fi:
res
end:
# iint
# Used ro replace Int or int and simply integrated expressions.
# Synopsis
# result := iint(a,b)
# Parameters
# a: integrated expression.
# b: integration variable.
# Description
# Used ro replace Int or int and simplify integrated expressions.
# Code
iint:=proc(a,b)
local a2,prov,prov2,prov3,prov4,i,j:
a2:=expand(a):
if type(a2,`+`) then
   prov:=0:
   for i from 1 to nops(a2) do
       prov:=prov+iint(op(i,a2),b)
   od:
   RETURN(prov)
fi:
if type(a2,`*`) then
   prov:=1:
   prov2:=1:
   for i from 1 to nops(a2) do
       if has(op(i,a2),b) then
          prov:=prov*op(i,a2)
       else
          prov2:=prov2*op(i,a2)
       fi:
   od:
   if prov2=1 then
      for j from 1 to nops(prov) do
          prov2:=op(j,prov):
          if has(prov2,diff) and op(2,prov2)=b then
             prov3:=prov/prov2:
             prov4:=whichdervar(prov3):
             if not(has(prov4,b)) then
                prov:=op(1,prov2)*prov3-int(op(1,prov2)*diff(prov3,b),b):
                RETURN(prov)
             fi
          fi
      od:
      prov:=int(prov,b):
   else
      prov:=prov2*iint(prov,b)
   fi:
   RETURN(prov)
fi:
int(a,b)
end:
# intsimp
# Aplies substitution of int and Int to iint until no changes are made.
# Synopsis
# result:=intsimp(a)
# Parameters
# result: a maple expression.
# a: a maple expression.
# Description
# Aplies substitution of int and Int to iint until no changes are made.
# Code
intsimp:=proc(a)
local res,a2:
a2:=expand(a):
res:=eval(subs(int=iint,Int=iint,a2)):
if res<>a2 then RETURN(intsimp(res)) fi:
res
end:
# whichder
#
# Return the derivatives in a.
#
whichder:=proc(a)
local a2,res,i:
global SADE:
a2:=a:
a2:=eval(subs(Diff=DDD,a2)):
a2:=convert(expand(a2),diff):
a2:=eval(subs(DDD=Diff,a2)):
if not(has(a2,diff)) and not(has(a2,Diff)) and not(has(a2,D)) then RETURN({}) fi:
if op(1,a2)=diff or op(1,a2)=Diff then RETURN(a2) fi:
res:={}:
if type(a2,`+`) or type(a2,`*`) then
   for i from 1 to nops(a2) do
       res:=res union whichder(op(i,a2))
   od:
   RETURN(res)
fi:
for i from 1 to nops(a2) do
    res:=res union whichder(op(i,a2))
od:
if op(0,a2)=diff or op(0,a2)=Diff or has(op(0,a2),D) then RETURN({a2}) fi:
if op(0,a2)=eval and (op(0,op(1,a2))=diff or op(0,op(1,a2))=Diff) then RETURN({a2}) fi:
res
end:
# whichder2
#
# Returns all the derivatives in an expression including zero order derivatives (functions).
# a: a maple expression
# v: a set of dependent variables.
#
whichder2:=proc(a,v)
local a2,res,i:
if type(a,function) and setcont(op(0,a),v)<>{} then
   RETURN({a})
fi:
a2:=convert(expand(a),diff):
if op(1,a2)=diff then RETURN(a2) fi:
res:={}:
if type(a2,`+`) or type(a2,`*`) or type(a2,set) or type(a2,list) then
   for i from 1 to nops(a2) do
       res:=res union whichder2(op(i,a2),v)
   od:
   RETURN(res)
fi:
if not(has(a2,diff)) then
   RETURN(setcont(a,v))
fi:
if op(0,a2)=diff and setcont(a2,v)<>{}
   then RETURN({a2})
fi:
for i from 1 to nops(a2) do
    res:=res union whichder2(op(i,a2),v)
od:
res
end:
# whichder3
#
# Same as whichder but do not consider terms with D.
#
whichder3:=proc(a)
local a2,res,i:
global SADE:
a2:=a:
a2:=eval(subs(Diff=DDD,a2)):
a2:=convert(expand(a2),diff):
a2:=eval(subs(DDD=Diff,a2)):
if not(has(a2,diff)) and not(has(a2,Diff)) then RETURN({}) fi:
if op(1,a2)=diff or op(1,a2)=Diff then RETURN(a2) fi:
res:={}:
if type(a2,`+`) or type(a2,`*`) then
   for i from 1 to nops(a2) do
       res:=res union whichder3(op(i,a2))
   od:
   RETURN(res)
fi:
for i from 1 to nops(a2) do
    res:=res union whichder3(op(i,a2))
od:
if op(0,a2)=diff or op(0,a2)=Diff then RETURN({a2}) fi:
if op(0,a2)=eval and (op(0,op(1,a2))=diff or op(0,op(1,a2))=Diff) then RETURN({a2}) fi:
res
end:
# whichfunction
whichfunction:=proc(a)
local a2,res,i:
global SADE:
a2:=a:
if type(a2,function) then
   if type(op(1,a2),function) then
      RETURN(whichfunction(op(1,a2)))
   else
      RETURN({a2})
   fi
fi:
if type(a2,constant) or type(a2,name) then
   RETURN()
fi:
res:={}:
if type(a2,`+`) or type(a2,`*`) then
   for i from 1 to nops(a2) do
       res:=res union whichfunction(op(i,a2))
   od:
   RETURN(res)
fi:
for i from 1 to nops(a2) do
    res:=res union whichfunction(op(i,a2))
od:
res
end:
# inlist
# Tests if a list is part of another list
# Synopsis
# result:=inlist(a,b)
# Parameters
# result:  a boolean value.
# a: a list.
# b: a alist
# Description
# Tests if the list b is part of the list a.
# Code
inlist:=proc(a,b)
local i,j,a2,f:
if nops(b)>nops(a) then RETURN(false) fi:
a2:=a:
for i from 1 to nops(b) do
    if has(a2,b[i]) then
       j:=1:
       f:=true:
       while f and j<=nops(a2) do
             if a2[j]=b[i] then
                f:=false:
                a2[j]:=1
             fi:
             j:=j+1
       od:
    else
       RETURN(false)
    fi
od:
true
end:
# whichderlist
#
# Returns a list with all derivation variables in the set (or list) v, with repetitions.
#
whichderlist:=proc(a,v)
local res,a2:
res:=1:
a2:=a:
while has(a2,diff) do
      res:=res,op(setcont(op(2,a2),v)):
      a2:=op(1,a2)
od:
res:=[res]:
res:=[op(2..nops(res),res)]:
res
end:
# isitinteg
# Tests wether a given equation is a candidate for integration.
# Synopsis
# result:=isitinteg(eq)
# Parameters
# result: false or a set of functions.
# eq: a maple expression representing an equation.
# Description
# Tests wether a given equation is a candidate for integration. if so returns the sets of possible unknown functions
# relative to which the equation may be solved.
# Code
isitinteg:=proc(eq)
local i,j,v,v2,flag,sder2,p,n,s1,sder,fs,f,res:
global SADE:
fs:=setcont(eq,SADE[incognita]):
s1:=whichder2(eq,SADE[incognita]):
sder:=s1 minus fs:
fs:=setcont(sder,fs):
s1:=s1 minus sder:
res:={}:
for i from 1 to nops(sder) do
    f:=setcont(sder[i],SADE[incognita]):
    f:=f[1]:
    v2:=whichderlist(sder[i],SADE[_vars]):
    v:={op(v2)}:
    n:=nops(v2):
    if nops(v)=1 then
       v:=v[1]:
       flag:=true
    else
       flag:=false
    fi:
    j:=0:
#    sder2:=sder minus {sder[i]}:
#    while flag and j<nops(sder2) do
#          j:=j+1:
#          p:=setcont(sder2[j],SADE[_vars]):
#          if not(inlist(whichderlist(sder2[j],SADE[_vars]),v2)) then
#             if has(p,v) then
#                flag:=false
#             fi
#          else
#             if setcont(sder2[j],SADE[incognita])<>{f} and s1<>{} then
#                flag:=false
#             fi
#          fi
#    od:
    if flag and has(s1 minus {f},v) then
       flag:=false
    fi:
    if flag then
       res:=res union {f}
    fi
od:
if res={} then
   RETURN(false)
fi:
res
end:
# whichdervar
#
# Returns the set of variable names which appear as derivation variables in the expression in a.
#
whichdervar:=proc(a)
local res,a2:
global SADE:
res:={}:
a2:=a:
while has(a2,diff) do
      res:=res union setcont(op(2,a2),SADE[_vars]):
      a2:=op(1,a2)
od:
res
end:
# derdeg
# Returns the number of times a function is derived in an expression, taking care of all redundancies.
# Synopsis
# result:=derdeg(a,f)
# Parameters
# result: a set o variable names.
# a: a maple expression
# f: a function.
# Description
# Returns the number of times aq function is derived in an expression, taking care of all redundancies.
# This corresponds to the number of arbitrary constants when the corresponding differential equation is solved.
# Code
derdeg:=proc(a,f)
local n,m,k,kc,i,j,l,p,p2,p3,nr:
p:=whichder(a):
p2:={}:
for i from 1 to nops(p) do
    if has(p[i],f) then
       p2:=p2 union {p[i]}
    fi
od:
m:=nops(p2):
if m=0 then RETURN(0) fi:
p:=array(1..m):
for i from 1 to m do
    p[i]:=op(2,p2[i]):
    p3:=op(1,p2[i]):
    while has(p3,diff) do
          p[i]:=p[i],op(2,p3):
          p3:=op(1,p3):
    od:
    p[i]:=[p[i]]
od:
p3:={op(p[1])}:
for i from 2 to m do
    p3:=p3 intersect {op(p[i])}
od:
n:=0:
for i from 1 to nops(p3) do
    k:=nops(p[1]):
    kc:=0:
    for j from 1 to m do
        for l from 1 to nops(p[j]) do
            if p[j][l]=p3[i] then
               kc:=kc+1
            fi
        od:
        if kc<k then
           k:=kc
        fi
    od:
    n:=n+k
od:
nr:=-n*m+n:
for i from 1 to m do
    nr:=nr+nops(p[i])
od:
nr
end:
# tautoelim
#
# This routine eliminates tautologies from a set of boolean conditions or a set of sets
# of boolean conditions (the argument of the routine).
#
tautoelim:=proc(eqs)
local i,res:
if nargs=0 then RETURN({}) fi:
if eqs={} then RETURN(eqs) fi:
res:={}:
if type(eqs[1],set) then
   for i from 1 to nops(eqs) do
       res:=res union {tautoelim(eqs[i])}
   od:
   RETURN(res)
fi:
for i from 1 to nops(eqs) do
    if op(1,eqs[i])<>op(2,eqs[i]) then
       res:=res union {eqs[i]}
    fi
od:
res
end:
# setcont
# Returns the elements of a set found in an expression.
# Synopsis
# result := setcont(a,s)
# Parameters
# result : a set of variable names.
# a: a maple expression.
# s: a set of variable names.
# Description
# 
# Code
setcont:=proc(a,s)
local res,i:
res:={}:
for  i from 1 to nops(s) do
     if has(a,s[i]) then
        res:=res union {s[i]}
     fi
od:
res
end:
# setcontonly
#
# Returns the set of elements in a that contain b.
#
setcontonly:=proc(a,b)
local i,r:
r:={}:
for i from 1 to nops(a) do
    if has(a[i],b) then
       r:=r union {a[i]}
    fi
od:
r
end:
# simpfunc
#
# Simplifies a list of univariate functions intended for a decomposition of a alinear expansion in these functions.
#
simpfunc:=proc(f)
local fcs,fcs2,i,j,p,fs,und:
fcs:=f:
fcs:=simplify(fcs,symbolic):
if has(fcs,sin) or has(fcs,cos) or has(fcs,tan) or has(fcs,cot) or has(fcs,sec) or has(fcs,csc) then
#   fcs:=convert(fcs,sin):
   fcs:=combine(fcs,trig)
fi:
#fcs:=convert(fcs,sin):print(22,fcs):
fcs:=simplify(fcs,symbolic):
und:=proc(x) x end:
fcs:=eval(subs(abs=und,fcs)):
fcs:=simplify(fcs):
fcs2:=fcs:
for i from 1 to nops(fcs) do
for j from i+1 to nops(fcs) do
    p:=fcs[j]/fcs[i]:
    p:=simplify(p):
    p:=simplify(p,trig):
    p:=expand(simplify(p,symbolic)):
    if type(p,constant) then
       fcs2[j]:=fcs[i]*p:
    fi
od
od:
fcs2
end:
# integeq
# Integrates an equation with respect to one independent variable.
# Synopsis
# result:=integeq(eq,vars)
# Parameters
# result: a list or the value false.
# qe: a differential equation.
# vars: a list of (independent) variable names.
# Description
# Integrates an equation with respect to one independent variable if the resulting equation is simpler.
# Code
integeq:=proc(eq,vars)
local i,res,wd:
global SADE:
if has(eq,int) or has(eq,Int) or not(has(eq,diff)) then RETURN(false) fi:
wd:=whichdervar(eq):
for i from 1 to nops(vars) do
    if has(wd,vars[i]) then
       res:=eval(int(eq,vars[i])):
       if not(has(res,int)) then
          RETURN([res,vars[i]])
       fi
    fi
od:
false
end:
# simpprod
#
# Simplify each term in a product (to overturn a bug in MAPLE 10 simplify)
#
simpprod:=proc(a)
local b,p,r,r2,i,idd:
global SADE:
b:=a:
#b:=simplify(simplify(b,symbolic),trig):
idd:=proc(x) 1 end:
b:=factor(eval(subs(csgn=idd,b)));
if type(b,`*`) then
   r:=1:
   r2:=1:
   for i to nops(b) do
       p:=op(i,b):
       if setcont(p,SADE[incognita])<>{} or setcont(p,SADE[parameters])<>{} then
          r:=r*simpbynd(op(i,b))
       else
          r2:=r2*op(i,b)
       fi
   od:
   r2:=combine(simplify(r2,symbolic),trig):
   if r2=0 then
      r:=0
   fi:
   RETURN(r)
fi:
simplify(b,symbolic)
end:
# simpbynd
#
# Simplifies beyound simplify!
#
simpbynd:=proc(a)
local i,b,r1,r2,p,t,e1,e2,s1,s2:
b:=expand(a):
if type(b,`^`) then
   r1:=op(1,b):
   r2:=op(2,b):
   r1:=simpbynd(op(1,b))^simpbynd(op(2,b)):
   RETURN(r1)
fi:
if type(b,`+`) then
   r1:=0:
   for i from 1 to nops(b) do
       r1:=r1+simpbynd(op(i,b))
   od:
   RETURN(r1)
fi:
if type(b,`*`) then
   p:=table():
   r1:={}:
   s1:=1:
   for i from 1 to nops(b) do
       t:=op(i,b):
       if type(t,`^`) then
          e1:=op(1,t):
          e2:=op(2,t):
          if has(e2,r1) then
             p[e2]:=p[e2]*e1
          else
             r1:=r1 union {e2}:
             p[e2]:=e1
          fi:
       else
          s1:=s1*t
       fi:
   od:
   s1:=simplify(s1):
   s2:=1:
   for i from 1 to nops(r1) do
       t:=(p[r1[i]])^r1[i]:
       s2:=s2*t
   od:
   s1:=simplify(expand(s1*s2),symbolic):
   RETURN(s1):
fi:
simplify(b,symbolic):
end:
# safesubs
#
# Substitutes a single term or a product of terms by an expression.
#
safesubs:=proc(a,b,y)
local i,j,r,t1,t2,t0,n,k,_gh,v,p,p2,ntm,flg:
ntm:=proc(z) local k: if type(z,`+`) then k:=nops(z) else k:=1 fi end:
t1:=op(1,a):
t2:=op(2,a):
if type(t1,`*`)  then
   flg:=false:
   n:=nops(t1)
else
   flg:=true:
   n:=1
fi:
r:=expand(b):
v:={}:
if not(flg) then t0:=subsord({op(t1)}) fi:
for i from 1 to n do
    if flg then
       r:=subs(t1=cat(_gh,i),r)
    else
       r:=subs(op(i,t0)=cat(_gh,i),r)
    fi:
    v:=v union {cat(_gh,i)}
od:
for i from 1 to n do
    p:=0:
    k:=ntm(r):
    for j from 1 to ntm(r) do
        if k=1 then
           p2:=traperror(coeff(r,v[i]))
        else
           p2:=traperror(coeff(op(j,r),v[i],1))
        fi:
        if p2<>lasterror and setcont(p2,{y})={} then
           p:=p+p2
        fi
    od:
    r:=p
od:
r:=expand(b-t1*r+t2*r):
r
end:
# subsord
#
# Puts a list of functions in an order such that a given function is not part of all previsou functions.
#
subsord:=proc(f)
local i,j,v,n,k,old:
n:=nops(f):
v:=vector([op(f)]):
for i from 1 to n do
    k:=i:
    for j from 1 to n do
        if has(v[j],v[i]) then
           k:=j
        fi
    od:
    if k<>i then
       old:=v[i]:
       v[i]:=v[k]:
       v[k]:=old
   fi
od:
convert(v,list)
end:
# funcoeff
#
# Returns the coefficient of the function f in the expression a.
#
funcoeff:=proc(a,f,y)
local res,i,j,_gh,n,p,p2:
res:=expand(a):
res:=safesubs(f=_gh,res,y):
n:=nops(f):
p:=expand(res):
res:=0:
if not(type(p,`+`)) then p:=p+_gh fi:
for i from 1 to nops(p) do
    p2:=op(i,p):
    p2:=traperror(coeff(p2,_gh)):
    if p2<>lasterror then
       res:=res+p2
    fi
od:
#for i from 1 to nops(v) do
#    res:=coeff(res,v[i])
#od:
res
end:
# pppdsolve
#
# Solves a PDE system with respect to the functions that are derived in the equations.
#
pppdsolve:=proc(eqs,f)
local f2,i,p,r,n,k:
global SADE:
f2:={}:
for i from 1 to nops(eqs) do
    p:=setcont(whichder(eqs[i]),SADE[incognita]):
    f2:=f2 union p
od:
r:=[pdsolve(eqs,f2)]:
if nops(r)=1 then
   r:=r
else
   n:=nops(r[1]):
   k:=1:
   for i from 2 to nops(r) do
       if nops(r[i])>n then
          n:=nops(r[i]):
          k:=i
       fi
   od:
   r:=r[k]
fi:
r
end:
# singlered
#
# Reduces to the involutive form a single equation.
# Used to compatibilize dependencies of the unknowns.
#
singlered:=proc(eq)
local res,v,p,eq2:
global SADE:
eq2:=simpprod(eq):
v:=setcont(eq,SADE[incognita]):
p:=rifsimp({eq},[vop(v)]):
p:=p[Solved]:
p:=map(x->op(1,x)-op(2,x),p):
if nops(p)>1 then
   res:={op(p)}
else
   res:={eq}
fi:
res
end:
# compatred
#
# Reduces the first possible equation using singlered, starting from the smallest equation.
#
compatred:=proc()
local eqs,i,p,r,v,v2,ss3,fl,f:
global SADE:
#eqs:=sizeorder(SADE[_system][1]):
eqs:=expand(SADE[_system][1]):
fl:=algsimpdiff():
f:=fl:
while f do f:=algsimpdiff() od:
if fl then RETURN(true) fi:
if SADE[traceout]=true then
   print(``):
   print(`Trying to reduce a single equation for variable compatibility...`):
   print(``)
fi:
for i from 1 to nops(eqs) do
    p:=eqs[i]:
    v:=setcont(p,SADE[incognita]):
    v2:=setcont(p,SADE[parameters]):
    if v={} and v2={} then ERROR("I'm really sorry, but the system is inconsistent...") fi:
    v:=[op(v)]:
    if nops(p+_gh)-1<=SADE[partial_reduction] and v2={} then
       r:=traperror(rifsimp({p},v))
    else
       r:=lasterror
    fi:
    if r<>lasterror then
       r:=r[Solved]:
       r:=map(x->op(1,x)-op(2,x),r):
       r:={op(r)}:
       if nops(r)>1 and not(has(SADE[_compatnoeqs],r)) then
          SADE[_compatnoeqs]:=SADE[_compatnoeqs] union {r}:
          eqs:={op(eqs)} minus {p}:
          eqs:=eqs union r:
          SADE[_system]:=[eqs,SADE[_system][2],SADE[_system][3]]:
          if SADE[traceout]=true then
             print(``):
             print(`reduced.`):
             print(``)
          fi:
          RETURN(true)
       fi
    fi
od:
false
end:
# orderfunctions
#
# Orders the list or set of functions in a, output is a list, such that
# the i-th element is not part of th j-th element whenever i<j.
#
orderfunctions:=proc(a)
local i,j,b,fcs,f,pr,_gH,fl,res:
if nops(a)=1 then
   RETURN(a)
fi:
if nops(a)=0 then
   RETURN({})
fi:
fcs:={op(a)}:
fl:=true:
i:=1:
while fl and i<=nops(fcs) do
      fl:=false:
      j:=1:
      b:=fcs[i]:
      while not(fl) and j<=nops(fcs) do
            if i<>j then
               pr:=subs(b=_gH,fcs[j]):
               if pr<>fcs[j] then fl:=true fi:
########################
               if {op(fcs[i])} intersect {op(fcs[j])}={op(fcs[i])} then fl:=true fi:
########################
            fi:
            j:=j+1
      od:
      i:=i+1
od:
pr:={op(fcs)} minus {b}:
res:=[b,op(orderfunctions(pr))]:
res
end:
# Implementation - Symmetries
# liesymmetries
#
# Computes the Lie symmetries of a set of differential equations given by eqs, in the
# unknown functions in the list dep of the indepenendent variables in the list indep.
# The output is a list of two elements: the first is a set of symmetry generators and
# the second element is a set of contraints (if any) on the symmetry generators.
#
liesymmetries:=proc()
local i,j,eqs,dep,indep,r,r2,r2b,params,v,n,cls,p,p2,g,Sold,pr,reg,_nm,tp,eq2,regra,nome,u2,v2:
global SADE:
nome:=__ugb:
eqs:=args[1]:
SADE[_compatnoeqs]:={}:
if type(eqs,list) then
   eqs:={op(eqs)}
fi:
if not(type(eqs,set)) then
   eqs:={eqs}
fi:
dep:=args[2]:
SADE[_deps]:=dep:
if has({args},independent) then
   for i from 1 to nargs do
       if has(args[i],independent) then
          indep:=op(2,args[i])
       fi
   od
else
   indep:=map(x->op(x),{op(dep)})
fi:
SADE[_indeps]:=indep:
eq2:=regularize_eq(eqs,dep,nome):
dep:=map(x->op(0,x),dep):
regra:=eq2[2]:
eq2:=eq2[1]:
#########################################################################
if has({args},freefunctions) then
  for i from 1 to nargs do
       if has(op(i,[args]),freefunctions) then
          SADE[_freefunctions]:=op(2,op(i,[args])) union map(x->op(1,x),regra):
       fi
   od:
else
   SADE[_freefunctions]:={}
fi:
#########################################################################
params:={}:
for i from 3 to nargs do
    if nops(args[i])=2 and op(1,args[i])=parameters then
       params:=op(2,args[i])
    fi
od:
SADE[parameters]:=params:
symmetries(eq2,dep,indep):
if regra<>{} then
   SADE[_system]:=subs(regra,SADE[_system])
fi:
#if has({args},partial_inv) then
if nops(SADE[_system][1])<SADE[_num_partial_inv] then
   SADE[_partial_inv]:=rifs:
   SADE[_partial_inv_first]:=true
#   partial_involutive(tp)
else
   SADE[_partial_inv]:=false
fi:
if has({args},kolchin_ritt) then
   v2:=SADE[_vars]:
   u2:=map(x->op(0,x),SADE[_system][2]):
   pr:=traperror(KolchinRitt(SADE[_system][1],v2,u2,_purelex)):
   if pr<>lasterror then
      SADE[_system]:=[{op(pr)},SADE[_system][2],SADE[_system][3]]
   fi
fi:
if has({args},involutive) then
   pr:=traperror(DEtools[rifsimp]([op(SADE[_system][1])],SADE[_system][2])):
   if pr<>lasterror then
      pr:=map(x->op(1,x)-op(2,x),pr[Solved]):
      SADE[_system]:=[{op(pr)},SADE[_system][2],SADE[_system][2]]
   else
      v2:=SADE[_vars]:
      u2:=map(x->op(0,x),SADE[_system][2]):
      pr:=traperror(KolchinRitt(SADE[_system][1],v2,u2,_purelex)):
      if pr<>lasterror then
         SADE[_system]:=[{op(pr)},SADE[_system][2],SADE[_system][3]]
      else
         error(`Unable to reduce the determining system to the involutive form`)
      fi
   fi
fi:
if params={} then
   if has({args},determining) then
      r:=[SADE[_system][1] minus {0},SADE[_system][2]]:
#      r:=SADE[_system][1..2]:
      SADE[_unks0]:=SADE[_system][2]:
   else
      SADE[_unks0]:=SADE[_system][2]:
      resolve():
      if SADE[_system][1]<>{} then resolve() fi:
      r:=sym_generators():
      SADE[_unks0]:={}
   fi
else
   v:=map(x->op(0,x),SADE[_system][2]):
   v:=[op(v),op(params)]:
   cls:=DEtools[rifsimp](SADE[_system][1],v,casesplit):
   n:=cls[casecount]:
   if not(type(n,integer)) then n:=1 fi:
   r:={}:
   eqtab(Sold,SADE):
   for i from 1 to n do
       if n=1 then
          SADE[_system][1]:=map(x->op(1,x)-op(2,x),{op(cls[Solved])}):
          p:={}:
          p2:={g=g}
       else
          eqtab(SADE,Sold):
          SADE[_system][1]:=map(x->op(1,x)-op(2,x),{op(cls[i][Solved])}) minus params:
          if not(has(cls[i][Case],"false split")) then
             p:={}:
             pr:=cls[i][Case]:
             for j from 1 to nops(pr) do
                p:=p union {op(map(x->if setcont(x,SADE[var])={} then x else 0 fi,pr[j]))}:
                p:=p minus {0}
             od:
             p2:=map(x->if setcont(x,SADE[var])={} then x else 0 fi,cls[i][Solved]):
             p2:={op(p2)} minus {0}:
             p:=p union p2:
             p:=map(x->if type(x,`=`) or type(x,`<>`) then x else 0 fi,p) minus {0}:
             p2:=map(x->if type(x,`=`) then x else 0 fi,p) minus {0}
          fi
       fi:
#############
#       SADE[incognita]:=SADE[incognita] union SADE[parameters]:
#############
       resolve():
       r2:=sym_generators():
       r2b:=r2:
       r2:=traperror(subs(p2,r2)):
       if r2<>lasterror then
          r2:=[eval(r2[1]) minus {0},r2[2] minus {0}]:
          p2:=traperror(solve(p,params)):
          if {p2}={} then
             r2={}:
             p2:={}
          fi: 
          if p2<>lasterror then
             p:=p2:
             if p<>{} then
                p:=map(x->if op(1,x)=op(2,x) then 0 else x fi,p) minus {0}
             fi
          fi:
          r2:=[r2,p]:
          r:=r union {r2}
       fi
   od:
   SADE[_freefunctions]:={}:
   SADE[_partial_inv]:=false:
   RETURN(r):
fi:
SADE[_freefunctions]:={}:
for i from 1 to nops(r[2]) do
    if setcont(r[2][i],{op(dep),op(indep)})={} then
       RETURN([{},{}])
    fi
od:
SADE[_partial_inv]:=false:
r
end:
# symmetries
#
# Obtains the determining system for the Lie Symmetries of a system of differential equations.
# The system must be given as a set of Maple expressions which are implicitly considered equal to zero,
# and using the Diff operator to represent differentiation.
#
symmetries:=proc(eqs,dep,indep)
local i,eqs2,eqs3,dep2:
global SADE:
if not(type(eqs,list)) and not(type(eqs,set)) then
   eqs2:={eqs}
else
   eqs2:=eqs
fi:
eqs3:={}:
for i from 1 to nops(eqs2) do
    if type(eqs2[i],`=`) then
       eqs3:=eqs3 union {op(2,eqs2[i])-op(1,eqs2[i])}
    else
       eqs3:=eqs3 union {eqs2[i]}
    fi
od:
if type(dep[1],function) then
   dep2:=map(x->op(0,x),dep)
else
   dep2:=dep
fi:
infsym(eqs3,dep,indep):
NULL
end:
# ncsymmetries
#
# Computes all non-classical symetries of the system eq in the unknowns u.
#
ncsymmetries:=proc(eqin,u)
global SADE:
local unk,v,s,i,j,j1,j2,k,n,g,p,p2,p3,cc,fc,eqs,flag,sl,fold,eq,dets,indep,
      n1,n2,o1,o2,o3,o4,params,unkopt:
if has({args},default_parameters) then
   o1:=SADE[_nlsimplify]:
   o2:=SADE[_ne]:
   o3:=SADE[timelim]:
   o4:=SADE[_timeinvol]:
   SADE[_nlsimplify]:=true:
   SADE[_ne]:=10:
   SADE[timelim]:=1:
   SADE[_timeinvol]:=60:
fi:
if type(eqin,list) then
   eq:={op(eqin)}
else
   eq:=eqin
fi:
if not(type(eq,set)) then
   eq:={eq}
fi:
if type(eq[1],`=`) then
   eq:=map(x->op(1,x)-op(2,x),eq)
fi:
if not(type(SADE[_timeinvol],constant)) then
   SADE[_timeinvol]:=-1
fi:
fold:=SADE[_subsflag]:
SADE[_subsflag]:=true:
SADE[_compatnoeqs]:={}:
SADE[_nlfname]:=_p:
SADE[_nlfcount]:=1:
indep:=map(x->op(x),{op(u)}):
if has({args},case) then
   i:=1:
   while not(has(args[i],case)) do i:=i+1 od:
   n1:=op(2,args[i]):
   if not(type(n1,integer)) or n1<1 or n1>nops(indep) then
      ERROR("Incorrect case number.")
   fi:
   n2:=n1
else
   n1:=1:
   n2:=nops(indep)
fi:
if has({args},determining) then
   dets:=1:
   for i from n1 to n2 do
       dets:=dets,nclass_det(eq,u,i)
   od:
   dets:=[dets]:
   dets:=dets[2..nops(dets)]: 
   dets:=map(x->[op(x),SADE[_vars]],dets):
   if n1=n2 then
      dets:=op(dets)
   fi:
   RETURN(dets)
fi:
n:=nops(u[1]):
g:={}:
cc:=1:
fc:=1:
for i from n1 to n2 do
    sl:=nclass_det(eq,u,i):
    v:=SADE[_vars]:
    s:=sl[2]:
    unk:=[op({op(sl[2])} minus {1,0})]:
       if has({args},builtin) then
          unkopt:=unk,builtin
       else
          unkopt:=unk
       fi:
       if has({args},involutive) then
          p:=simplify(nonlindsolve(sl[1],unkopt,involutive))
       else
          p:=traperror(simplify(nonlindsolve(sl[1],unkopt))):
          if p=lasterror then p:={} fi:
       fi:
       j1:=1:
       while has(p,cat(_C,j1)) do
             p:=subs(cat(_C,j1)=cat(_c,cc),p):
             cc:=cc+1:
             j1:=j1+1
       od:
       j2:=1:
       while has(p,cat(_F,j2)) do
             p:=subs(cat(_F,j2)=cat(_f,cc),p):
             cc:=cc+1:
             j2:=j2+1
       od:
       for k from 1 to SADE[_nlfcount] do
           p2:=cat(SADE[_nlfname],k):
           p3:=searchfunction(p,p2):
           if has(p,p2) then
              if type(p3,function) then
                 p:=subs(p2=cat(_F,j2),p):
                 j2:=j2+1
              else
                 p:=subs(p2=cat(_C,j1),p):
                 j1:=j1+1
              fi
           fi
       od:
       for k from 1 to nops(p) do
           p2:=0:
           for j from 1 to nops(v) do
               p2:=p2+subs(p[k][1],s[j])*D[v[j]]
           od:
           p3:=p[k][2] minus {0}:
           if p3<>{} then
              p2:=[p2,p3]
           fi:
           g:=g union {p2}
       od
od:
SADE[_substitutions]:={}:
SADE[_subsflag]:=fold:
if has({args},default_parameters) then
   SADE[_nlsimplify]:=o1:
   SADE[_ne]:=o2:
   SADE[timelim]:=o3:
   SADE[_timeinvol]:=o4
fi:
g      
end:
# LBsymmetries
#
# Determines Lie-Backlund symmetries of equation(s) ind eqs_in, in the functions in funcs,
# and with generator coefficient depending on variables in ders. 
#
LBsymmetries:=proc(eqs_in,funcs::list,ders)
local i,j,k,l,m,eqs,ortho,u,v,u2,sders,flag,pr,eqsders,edeqs,deder,decold,
      edu,eduvars,Q,Qarg,deteqs,de,_u,regra,regra2,regra3,edeqs0,sdv,_xi,te,unkQ,r,
      regra2b:
global SADE:
if type(eqs_in,set) then
   eqs:=eqs_in
else
   eqs:={eqs_in}
fi:
if type(eqs[1],`=`) then
   eqs:=map(x->op(1,x)-op(2,x),eqs)
fi:
u:=map(x->op(0,x),funcs):
v:=[op({op(map(x->op(x),funcs))})]:
# Compute the orthonomic form of the differential system
ortho:=orthoform(eqs,v,u):
# Determines the dependent and independent derivatives on which the symmetries depend.
sders:=ders:
flag:=true:
while flag do
      pr:=sders:
      for i from 1 to nops(ortho) do
          pr:=subeq(ortho[i],pr,v,u)
      od:
      pr:=whichder(pr):
      if pr=sders then
         flag:=false
      fi:
      sders:=pr
od:
eqsders:=orddiff(map(x->op(whichder(x)),eqs),v,u):
edeqs:=map(x->x[1],eqsders):
eqsders:=map(x->x[4],eqsders):
pr:=orddiff(whichder(sders),v,u):
edu:=map(x->op(1,x),pr):
eduvars:=map(x->op(4,x),pr):
Q:=array(1..nops(funcs)):
Qarg:=[op(funcs),op(v),op(sders)]:
regra:={}:
edeqs0:=edeqs:
for i from 1 to nops(edeqs) do
    eqs:=subs(edeqs[i]=cat(_u,i),eqs):
    edeqs0:=subs(edeqs[i]=cat(_u,i),edeqs0):
    regra:=regra union {cat(_u,i)=edeqs[i]}
od:
Qarg:=op(Qarg):
te:={}:
unkQ:=0:
for i from 1 to nops(funcs) do
    Q[i]:=cat(eta,i)(Qarg):
    unkQ:=unkQ,Q[i]:
    te:=te union {cat(eta,i)}
od:
unkQ:=[unkQ]:
unkQ:=unkQ[2..nops(unkQ)]:
deteqs:={}:
for i from 1 to nops(eqs) do
    de:=0:
    for j from 1 to nops(funcs) do
        pr:=subs(funcs[j]=_u,eqs[i]):
        pr:=diff(pr,_u):
        pr:=subs(_u=funcs[j],pr):
        de:=de+Q[j]*pr
    od:
    for k from 1 to nops(eqsders) do
        pr:=eqsders[k]:
        for j from 1 to nops(funcs) do
            sdv:=0:
            for l from 1 to nops(pr) do
                if pr[l]<>0 then
                   sdv:=sdv,seq(v[l],m=1..pr[l])
                fi
             od:
             if has(eqs[i],edeqs0[k]) then
                sdv:=[sdv]:
                sdv:=sdv[2..nops(sdv)]:
                de:=de+diff(eqs[i],edeqs0[k])*diff(Q[j],op(sdv))
             fi
        od
    od:
    de:=subs(regra,de):
    deteqs:=deteqs union {de}
od:
flag:=true:
deteqs:=map(x->x=0,deteqs):
while flag do
      pr:=deteqs:
      for i from 1 to nops(ortho) do
          pr:=subeq(ortho[i],pr,v,u)
      od:
      if pr=deteqs then
         flag:=false
      fi:
      deteqs:=pr
od:
deteqs:=map(x->op(1,x)-op(2,x),deteqs):
deder:=map(x->if setcont(x,te)={} then x else 0 fi,whichder(deteqs)) minus {0}:
deder:=deder minus {op(edu)}:
pr:=traperror(map(x->coeffs(expand(x),deder),deteqs)):
if pr=lasterror then
   decold:=SADE[_decompvar]:
   SADE[_decompvar]:=deder:
   SADE[_nolifdecindep]:=true:
   deteqs:=map(z->op(coeffgen(conv_diff(expand(z)),dep,indep)),deteqs):
   SADE[_nolifdecindep]:=false:
   SADE[_decompvar]:=decold
else
   deteqs:=pr
fi:
u2:=0:
regra2:=0:
regra3:={}:
for i from 1 to nops(edu) do
    regra2:=regra2,edu[i]=cat(_xi,i):
    regra3:=regra3 union {cat(_xi,i)=edu[i]}:
    u2:=u2,cat(_xi,i)
od:
regra2:=[regra2]:
regra2:=regra2[2..nops(regra2)]:
regra2b:=convert(regra2,D):
u2:=[u2]:
u2:=u2[2..nops(u2)]:
deteqs:=subs(regra2,deteqs):
deteqs:=subs(regra2b,deteqs):
unkQ:=subs(regra2,unkQ):
for i from 1 to nops(funcs) do
    pr:=funcs[i]:
    deteqs:=subs(pr=op(0,pr),deteqs):
    unkQ:=subs(pr=op(0,pr),unkQ)
od:
deteqs:=convert(deteqs,diff):
SADE[fcount]:=1:
SADE[fname]:=_q:
SADE[var]:=[op(u),op(v),op(u2)]:
SADE[_vars]:=SADE[var]:
SADE[_decompvar]:=SADE[var]:
SADE[incognita]:={op(unkQ)}:
if has({args},involutive) then
   pr:=traperror(rifsimp(deteqs,[op(unkQ)])):
   if pr<>lasterror then
      deteqs:=map(x->op(1,x)-op(2,x),pr[Solved]):
      deteqs:={op(deteqs)}
   fi
fi:
SADE[_system]:=[{op(deteqs)},unkQ,{}]:
if has({args},determining) then
   RETURN([{op(deteqs)},unkQ,regra3])
fi:
resolve():
r:=sym_generators():
r:=subs(regra3,r):
r:=[r[1],r[2],sders]:
r:=convert(r,Diff):
for i from 1 to nops(funcs) do
    r:=subs(funcs[i]=op(0,funcs[i]),r)
od:
r
end:
# nclass_det
#
# Returns the determining equations for non-classical symmetries for the equations in eqs, with
# dependente variables in fs. The value of m specifies which theta.m is set equal to 1 or 0.
#
#
# Returns the determining equations for non-classical symmetries for the equations in eqs, with
# dependente variables in fs. The value of m specifies which theta.m is set equal to 1 or 0.
#
nclass_det:=proc(eqs,fs,m)
local i,j,r,bestvar,vars,funcs,f0,invconds,pr,_eta,_theta,nms,dvs,se,bvp,
      eqs2,eqsubs,flag,eqsimp,newfs,_A,regra,regra2,detsyst,bv0,nv,sdvars:
global SADE:
vars:=[op({op(map(x->op(x),fs))})]:
funcs:=[op(setcont(eqs,fs))]:
bestvar:=bestdiffvar(eqs,vars,funcs):
bv0:=bestvar[m]:
invconds:={}:
nms:=op(funcs),op(vars):
dvs:={}:
newfs:={}:
for i from 1 to nops(funcs) do
    pr:=cat(_eta,i)(nms):
    newfs:=newfs union {cat(_eta,i)}:
    for j from 1 to nops(vars) do
        pr:=pr-diff(funcs[i],vars[j])*cat(_theta,j)(nms):
        newfs:=newfs union {cat(_theta,j)}:
    od:
    invconds:=invconds union {pr}:
    dvs:=dvs union {diff(funcs[i],bv0)}
od:
#print(1111):
pr:=cat(_theta,posvars(bv0,vars))(nms)=1:
for i from 1 to m-1 do
    bvp:=posvars(bestvar[i],vars):
    pr:=pr,cat(_theta,bvp)(nms)=0
od:
invconds:=subs(pr,invconds):
se:=solve(invconds,dvs):
regra2:={pr}:
SADE[_substitutions]:=se:
f0:=map(x->op(0,x),funcs):
eqsimp:={}:
#print(2222):
for i from 1 to nops(eqs) do
    flag:=true:
    eqs2:=simplify(eqs[i])=0:
    while flag do
          eqsubs:=conv_diff(eqs2):
          for j from 1 to nops(invconds) do
              eqsubs:=conv_diff(simplify(eval(subeq(se[j],eqsubs,vars,f0)))):
          od:
          if eqsubs=eqs2 then
             flag:=false
          fi:
          eqs2:=eqsubs
    od:
    eqsimp:=eqsimp union {eqsubs}
od:
#print(3333):
eqsimp:=convert(eqsimp,D):
eqsimp:=conv_diff(map(x->op(2,x)-op(1,x),eqsimp)):
eqsimp:=convert(eqsimp,D):
dvs:=map(x->convert(x,D),setcontonly(whichder(eqsimp),newfs)):
regra:={}:
for i from 1 to nops(dvs) do
    pr:=cat(_A,i)(nms):
    eqsimp:=subs(dvs[i]=pr,eqsimp):
    regra:=regra union {pr=dvs[i]}
od:
for i from 1 to nops(funcs) do
    regra:=subs(funcs[i]=f0[i],regra)
od:
#print(4444):
regra:=conv_diff(regra):
eqsimp:=conv_diff(eqsimp):
#print(44,A,eqsimp,funcs):
pr:=liesymmetries(eqsimp,funcs,determining):
#print(44,B):
pr:=eval(subs(regra,pr)):
eqsimp:=pr[1]:
nms:=op(f0),op(vars):
sdvars:=pr[2]:
#print(44,C):
for i from 1 to nops(f0) do
    nv:=posvars(f0[i],SADE[_vars]):
    eqsimp:=subs(cat(_eta,nv)(nms)=pr[2][i],eqsimp)
od:
#print(5555):
regra2:=subs(op(map(x->x=op(0,x),funcs)),regra2):
for i from 1 to nops(vars) do
    nv:=posvars(vars[i],SADE[_vars]):
    eqsimp:=subs(cat(_theta,nv-nops(f0))(nms)=pr[2][i+nops(f0)],eqsimp):
    regra2:=subs(cat(_theta,nv-nops(f0))(nms)=pr[2][i+nops(f0)],regra2)
od:
eqsimp:=eval(subs(regra2,eqsimp)) minus {0}:
sdvars:=subs(regra2,sdvars):
[eqsimp,sdvars]
end:
# ansatz
#
# Performs an ansatz on the determining system of equations.
# The first argument is a substitution rule or a set of such rules
# of the form unknown=functional form, which may involve arbitrary
# constants or functions, which must be specified as the second argument.
#
ansatz:=proc()
local i,r,s,u:
global SADE:
r:=args[1]:
if not(type(r,set)) then
   r:={r}
fi:
u:=args[2]:
if not(type(u,set)) then
   u:={u}
end:
s:={}:
for i from 1 to nops(r) do
    s:=s union {op(1,r[i])}
od:
replace(r):
SADE[incognita]:=SADE[incognita] union u:
SADE[incognita]:=SADE[incognita] minus s:
if has({args},determining) then
   r:=SADE[_system][1]
else
   resolve():
   r:=sym_generators()
fi:
r
end:
# infsym
#
# Implements the infinitesimal symmetry conditions.
#
infsym:=proc(eqs,dep,indep)
local i,j,ortf,rule1,rule2,rule3,rule4,p,pb,p2,p3,ds,ds2,vd,fnc,dep2,eqs2,eqs3,
      r,eta,etheta,unk,trinf,trinf2,trinf3,flag,old,wd,decold,derivatives,u,v,_DR,
      derivs,pr,wdrl,oldincog:
global SADE:
if has(eqs,Diff) then
   eqs2:=conv(eqs,dep,indep)
else
   eqs2:=eqs
fi:
wdrl:=which_der_present(eqs2):
eqs3:=eqs2:
u:=[op(dep)]:
v:=[op(indep)]:
derivatives:=wder(eqs2,dep):
derivatives:=map(x->x[1],orddiff(derivatives,v,u)):
for i from 1 to nops(derivatives) do
    eqs2:=subs(derivatives[i]=cat(_DR,i),eqs2)
od:
eqs2:=[op(derivatives),eqs2]:
dep2:=1:
for i from 1 to nops(dep) do
    eval(subs(dep[i]=funcdep,eqs2)):
    p:=SADE[_funcdep]:
    dep2:=dep2,dep[i](op(p))
od:
dep2:=[dep2]:
dep2:=[op(2..nops(dep2),dep2)]:
if nargs=3 then 
   ortf:=traperror(orthoform(eqs3,indep,dep)):
   if ortf=lasterror then
      error "Unable to obtain the input equation(s) in orthonomic form"
   fi
fi:
vd:={}:
rule1:={}:
rule2:={}:
rule3:={}:
rule4:={}:
trinf:={}:
trinf2:={}:
trinf3:={}:
unk:=1:
for i from 1 to nops(dep) do
    rule3:=rule3 union {dep2[i]=dep[i]}:
    rule4:=rule4 union {dep[i]=dep2[i]}:
    fnc:=cat(eta,i):
    trinf:=trinf union {dep[i]=dep[i]+_eps*fnc(op(dep),op(indep))}:
    trinf2:=trinf2 union {dep2[i]=dep2[i]+_eps*fnc(op(dep2),op(indep))}:
    unk:=unk,fnc(op(dep),op(indep))
od:
for i from 1 to nops(indep) do
    fnc:=cat(theta,i):
    trinf:=trinf union {indep[i]=indep[i]+_eps*fnc(op(dep),op(indep))}:
    trinf3:=trinf3 union {indep[i]=indep[i]+_eps*fnc(op(dep),op(indep))}:
    unk:=unk,fnc(op(dep),op(indep))
od:
unk:=[unk]:
unk:=unk[2..nops(unk)]:
SADE[_depvars]:=dep:
SADE[_depvars2]:=dep2:
SADE[_indepvars]:=indep:
eqs2:=map(x->uptoone(eval(subs(trinf2,x)),_eps),eqs2):
if nargs=4 then
   r:=wder(eqs2,dep)
else
   r:=setcont(eqs2,wdrl)
fi:
ds:={}:
for i from 1 to nops(r) do
    if setcont(r[i],dep2)<>{} then
       ds:=ds union {r[i]}
    fi
od:
ds:=[op(ds)]:
for i from 1 to nops(ds) do
    p:=whichderlist2(ds[i],indep):
    fnc:=cat(_d,op(1,setcont(ds[i],dep))):
    for j from 1 to nops(p) do
        fnc:=cat(fnc,p[j])
    od:
    vd:=vd union {fnc}:
    rule1:=rule1 union {ds[i]=fnc}:
    rule2:=rule2 union {fnc=ds[i]}
od:
ds:=[op(ds)]:
rule2:=convert(rule1,D):
eqs2:=map(x->subs(rule2,convert(x,D)),eqs2):
eqs2:=map(x->conv_diff(subs(rule3,x)),eqs2):
eqs2:=map(x->uptoone(x,_eps),eqs2):
eqs2:=map(z->map(x->subs(trinf3,coeff(x,_eps,0))+_eps*coeff(x,_eps,1),z),eqs2):
eqs2:=map(x->subs(map(x->op(2,x)=op(1,x),rule1),x),eqs2):
r:=wder(eqs2,dep):
derivs:=map(x->if setcont(x,dep2)={} then 0 else x fi,r) minus {0}:
ds:={}:
for i from 1 to nops(r) do
    if setcont(r[i],dep2)<>{} then
       ds:=ds union {r[i]}
    fi
od:
ds:=[op(ds)]:
eqs2:=convert(eqs2,D):
ds2:=subs(diff=Diff,ds):
ds2:=subs(rule3,ds2):
ds2:=expand(eval(subs(Diff=dtot,ds2))):
ds:=convert(ds,D):
for i from 1 to nops(ds) do
    eqs2:=map(x->subs(ds[i]=ds2[i],x),eqs2):
    eqs2:=[op(uptoone(eqs2[1..nops(eqs2)-1],_eps)),eqs2[nops(eqs2)]]:
od:
derivs:=wdrl:
eqs2:=map(x->uptoone(x,_eps),eqs2):
eqs3:=eqs2[nops(eqs2)]:
for i from 1 to nops(derivatives) do
    eqs3:=subs(cat(_DR,i)=eqs2[i],eqs3)
od:
eqs2:=map(x->coeff(uptoone(x,_eps),_eps),eqs3):
if nargs=3 then
   eqs2:=subs(ortf,eqs2):
   derivs:=derivs minus map(x->op(1,x),ortf):
   if type(SADE[_substitutions],set) and SADE[_substitutions]<>{} then
      eqs2:=suball(SADE[_substitutions],eqs2,dep2):
      SADE[_substitutions]:={}
   fi
fi:
eqs2:=expand(eqs2):
if type(eqs2[1],`=`) then
   eqs2:=map(x->op(2,x)-op(1,x),eqs2)
fi:
r:=derivs:
SADE[incognita]:={op(unk)}:
#
# Here we return if only the corresponding prolongation is required
#
if nargs=4 then RETURN(eqs2) fi:
eqs2:=map(x->numer(x),eqs2):
p:=traperror(map(x->coeffs(expand(x),r),eqs2)):
if p=lasterror then
   decold:=SADE[_decompvar]:
   SADE[_decompvar]:=r:
   SADE[_nolifdecindep]:=true:
######################################################################################
   oldincog:=SADE[incognita]:
   for i from 1 to nops(oldincog) do
       if type(oldincog[i],function) then
          SADE[incognita]:=SADE[incognita] union {op(0,oldincog[i])}
       else
          SADE[incognita]:=SADE[incognita] union {oldincog}
       fi
   od:
######################################################################################
   eqs2:=map(z->op(coeffgen(conv_diff(expand(z)),dep,indep)),eqs2):
   SADE[incognita]:= oldincog:
   SADE[_nolifdecindep]:=false:
   SADE[_decompvar]:=decold
else
   eqs2:=p
fi:
eqs2:=subs(rule3,eqs2):
eqs2:=convert(eqs2,diff):
SADE[fcount]:=1:
SADE[fname]:=_q:
SADE[var]:=[op(dep),op(indep)]:
SADE[_vars]:=SADE[var]:
SADE[_decompvar]:=SADE[var]:
SADE[_system]:=[{op(eqs2)},unk,{}]:
single_diff_single_var():
end:
# single_diff_single_var
#
# Replaces in the determining system all equations of the form diff(f,x)
# where f in any unkwnon.
#
single_diff_single_var:=proc()
local i,j,eqs,eqs2,eqs3,pr,pr2,pr3,dp,res,n1,n2:
global SADE:
n1:=SADE[_system][1] minus {0}:
eqs:=Array([op(SADE[_system][1])]):
dp:=SADE[_deps]:
dp:=map(x->op(0,x),SADE[_deps]):
eqs2:={}:
for i from 1 to nops(SADE[_system][1]) do
    pr:=eqs[i]:
    if not(type(pr,`+`)) and has(pr,diff) then
       if type(pr,`*`) then
          pr2:=1:
          for j from 1 to nops(pr) do
              pr3:=op(j,pr):
              if has(pr3,diff) or setcont(pr3,SADE[_freefunctions])<>{} then
                 pr2:=pr2*pr3
              fi
          od:
          pr:=pr2
       fi:
       pr2:=whichderlist(pr,dp):
       if nops(pr2)=1 then
          eqs2:=eqs2 union {pr}
       fi
    fi
od:
eqs2:=clean_eqs(eqs2,SADE[incognita]):
eqs3:=map(x->x=0,eqs2):
res:=eval(subs(eqs3,SADE[_system][1])) minus {0}:
res:=res union eqs2:
n2:=res:
SADE[_system]:=[res,SADE[_system][2],SADE[_system][3]]:
if n1<>n2 then
   single_diff_single_var()
fi:
res
end:
# which_der_present
#
# Returns all derivatives of the dependent variables present in the invariance conditions.
#
which_der_present:=proc(eqs)
local i,i2,j,k,res,wde,wde2,pr,pr2,dp,vr_list,vr_list2,vr,newders,ndr:
global SADE:
wde:=wder(eqs,SADE[_deps]):
pr2:=map(x->whichderlist(x,SADE[_indeps]),[op(wde)]):
wde2:={}:
for i from 1 to nops(SADE[_deps]) do
for j from 1 to nops(SADE[_indeps]) do
    wde2:=wde2 union {diff(SADE[_deps][i],SADE[_indeps][j])}
od
od:
newders:={}:
for i from 1 to nops(pr2) do
    vr_list:=pr2[i]:
    for j from 1 to nops(pr2[i]) do
        vr_list2:=combinat[permute](pr2[i],j):
        ndr:=map(z->op(map(x->diff(z,op(x)),vr_list2)),SADE[_deps]):
        newders:=newders union {op(ndr)}:
        if j=nops(pr2[i])-1 then
           newders:=newders union {op(map(z->op(map(x->diff(x,z),wde2)),vr_list2))}
        fi
    od:
od:
newders:=newders union wde union wde2:
newders
end:
# coeffgen
#
# Computes the coefficients of independent functions of the derivatives of
# the dependent variables in y with respect to the dependent variables on x.
#
coeffgen:=proc(eqs,y,x)
local i,j,p,p2,p3,y2,eqs2,eqs3,eq3,un,_wgh,old,fl:
global SADE:
p2:=whichder(eqs):
p:={}:
for i from 1 to nops(p2) do
    fl:=true:
    p3:=p2[i]:
    j:=1:
    while fl and j<=nops(y) do
         if whoisdiff(p3,y[j]) then
            p:=p union {p3}:
            fl:=false
         fi:
         j:=j+1
    od
od:
p2:={}:
y2:=map(z->op(whichfunction(z)),p):
for i from 1 to nops(p) do
    if setcont(p[i],y2)<>{} then
       p2:=p2 union {p[i]}
    fi
od:
p2:=orddiff(p2,x,y):
p2:=map(z->z[1],p2):
un:={}:
eqs2:=eqs:
for i from 1 to nops(p2) do
    eqs2:=subs(p2[i]=cat(_wgh,i),eqs2):
    un:=un union {cat(_wgh,i)}
od:
old:=SADE[_decompvar]:
SADE[_decompvar]:=un:
eqs2:={simplify(eval(eqs2),assume=positive)}:
for i from 1 to nops(un) do
    eqs3:={}:
    for j from 1 to nops(eqs2) do
        p:=lifdec(eqs2[j],un[i]):
        eqs3:=eqs3 union p[1]
    od:
    eqs2:=eqs3
od:
SADE[_decompvar]:=old:
eqs2
end:
# eqtab
#
# Simply puts the table b in a new table a without both being constrained to one another.
#
eqtab:=proc(a,b)
local i,n,p,e,d:
p:=op(2,op(1,b)):
n:=nops(p):
a:=table():
for i from 1 to n do
    e:=op(1,p[i]):
    d:=op(2,p[i]):
    a[e]:=d
od:
a
end:
# uptoone
#
# Expands the expression in a up to first order in the parameter e.
#
uptoone:=proc(a,e)
local r,n:
if type(a,list) or type(a,set) then
   r:=map(x->uptoone(x,e),a):
   RETURN(r)
fi:
#n:=traperror(degree())
#r:=expand(a):
r:=a:
r:=subs(e=0,r)+subs(e=0,diff(r,e))*e:
#r:=expand(r):
r
end:
# dtot
#
# Computes the total derivative of a with respect to b.
#
dtot:=proc(a,b)
local j,k,r,dp,dp2,id,fnc,p:
global SADE:
dp:=SADE[_depvars]:
dp2:=SADE[_depvars2]:
id:=SADE[_indepvars]:
r:=0:
for j from 1 to nops(id) do
    fnc:=cat(theta,j):
    fnc:=fnc(op(dp),op(id)):
    p:=diff(a,id[j]):
    for k from 1 to nops(dp) do
        p:=p+diff(a,dp[k])*diff(dp2[k],id[j])
    od:
    if b=id[j] then
       r:=r+p
    fi:
    r:=r-_eps*p*diff(fnc,b):
    for k from 1 to nops(dp) do
        r:=r-_eps*p*diff(fnc,dp[k])*diff(dp2[k],b)
    od
od:
r:=uptoone(r,_eps):
r
end:
# funcdep
#
# Simply put in SADE[_funcdep] its arguments in the correct order.
# Used to obtain the arguments of a function by replacing its name by funcdep.
#
funcdep:=proc()
global SADE:
SADE[_funcdep]:=[args]:
_ff
end:
# wder
#
# Returns the set of derivatives with respect to the variables in dep in the expression a.
#
wder:=proc(a,dep)
local i,r,p:
p:=expand(a):
if type(p,`+`) or type(p,`*`) or type(p,set) or type(p,list) or type(p,`^`) or (type(p,function) and op(0,p)<>diff) then
   r:={}:
   for i from 1 to nops(p) do
       r:=r union wder(op(i,p),dep)
   od:
   RETURN(r)
fi:
if setcont(p,dep)<>{} and has(p,diff) then
   RETURN({p})
fi:
{}
end:
# conv
#
# Converts a system from the format with Diff to the usual
# maple notation for equations with diff.
#
conv:=proc(eqs,dep,indep)
local i,r:
r:=eqs:
for i from 1 to nops(dep) do
    r:=subs(dep[i]=dep[i](op(indep)),r)
od:
r:=subs(Diff=diff,r):
r
end:
# replace
#
# Applies the rule(s) r in the global variable SADE.
#
replace:=proc(r)
local i,eqs,prov,fs,rule:
global SADE:
rule:=r:
if not(type(rule,set)) then
   rule:={rule}
fi:
prov:={}:
for i from 1 to nops(rule) do
    if op(1,rule[i])<>op(2,rule[i]) then
       prov:=prov union {rule[i]}
    fi
od:
rule:=prov:
fs:={}:
for i from 1 to nops(rule) do
    fs:=fs union {op(1,rule[i])}
od:
SADE[_system][1]:=expand(subs(rule,SADE[_system][1])):
SADE[_system][2]:=subs(rule,SADE[_system][2]):
SADE[_system][3]:=subs(rule,SADE[_system][3]):
SADE[_system]:=expand(SADE[_system]):
if type(SADE[incognita],set) then
   for i from 1 to nops(rule) do
       SADE[incognita]:=SADE[incognita] minus {op(1,rule[i])}
   od:
   if nargs=2 then
      SADE[incognita]:=SADE[incognita] union args[2]
   fi
else 
   SADE[incognita]:={}
fi:
if nargs=2 then
   SADE[incognita]:=SADE[incognita] union args[2]
fi:
end:
# posvars
#
# Gives the position of a in the list vars. If a is not an element of vars it returns 0.
#
posvars:=proc(a,v)
local i:
if not(has(v,a)) then RETURN(0) fi:
for i from 1 to nops(v) do
      if a=op(i,v) then RETURN(i) fi
od
end:
# sym_generators
#
# Returns the set of symmetry generators obtained after using resolve.
#
sym_generators:=proc()
local i,j,fcont,ccont,unks,unks2,indep_unks,prov,prov2,syst,_C,_F,
      nm,nm2,res,res2,syst2,idd,d,zerofunc,incog:
global SADE:
idd:=proc(x) 1 end:
zerofunc:=proc(x) 0 end:
syst:=SADE[_system]:
unks:=setcont(simplify(syst[2]),SADE[incognita]):
unks2:=setcont(syst[1],unks):
indep_unks:=unks minus unks2:
fcont:=1:
ccont:=1:
unks2:=[op(unks2)]:
for i from 1 to nops(unks2) do
    nm:=unks2[i]:
    if type(nm,function) then
       nm:=op(0,nm):
       nm2:=cat(_F,fcont):
       fcont:=fcont+1
    else
       nm2:=cat(_C,ccont):
       ccont:=ccont+1
    fi:
    syst:=subs(nm=nm2,syst):
    unks2:=subs(nm=nm2,unks2)
od:
res:={}:
syst2:=eval(subs(op(map(x->x=0,unks2)),syst[2])):
for i from 1 to nops(indep_unks) do
    prov:=syst2:
    nm:=indep_unks[i]:
    if type(nm,function) then
       nm:=op(0,nm):
       nm2:=cat(_F,fcont):
       fcont:=fcont+1
    else
       nm2:=1
    fi:
    for j from 1 to nops(indep_unks) do
        if i=j then
           prov:=subs(nm=nm2,prov)
        else
           if type(indep_unks[j],function) then
              prov:=eval(subs(op(0,indep_unks[j])=zerofunc,prov))
           else
              prov:=subs(indep_unks[j]=0,prov)
           fi
        fi
    od:
    res:=res union {prov}
od:
syst2:=eval(subs(op(map(x->x=0,unks)),syst[2])):
res:=res union {syst2}:
res2:={}:
for i from 1 to nops(res) do
    prov:=0:
    for j from 1 to nops(SADE[_system][2]) do
        prov:=prov+res[i][j]*D[SADE[_vars][j]]
    od:
    res2:=res2 union {prov}
od:
incog:={}:
for i from 1 to nops(SADE[incognita]) do
    if type(SADE[incognita][i],function) then
       incog:=incog union {op(0,SADE[incognita][i])}
    else
       incog:=incog union {SADE[incognita][i]}
    fi
od:
res:={}:
for i from 1 to nops(res2) do
    prov:=factor(res2[i]):
    if type(prov,`*`) then
       prov2:=1:
       for j from 1 to nops(prov) do
           nm:=op(j,prov):
           if setcont(nm,SADE[_vars])<>{} then
              prov2:=prov2*nm
           fi
       od:
       prov:=prov2
    fi:
    if setcont(prov,incog)={} then
       res:=res union {prov}
    fi
od:
d:={}:
for i from 1 to nops(SADE[_vars]) do
    d:=d union {D[SADE[_vars][i]]}
od:
res:=collect(simplify(res),d):
res:=eval(subs(csgn=idd,res)) minus {0}:
[res,syst[1]]
end:
# noether
#
# Computes the Noether conserved currents.The firsdt argument of the input is the lagrangiam and the
# second argument is the list of dependent variables (with its arguments). An optional third
# argument is a symmetry generator of the action, and return the corresponding
# conserved current. The ouput is a set of conserved curents in the case of a single independent
# variable. For two or more independent variables, the output is a sequence of two elements:
# the set of conserved currents and the list of independent variables in the corresponding
# order of the components of the conserved currents.
#
noether:=proc()
local i,j,k,prov,provaux,prov1,prov2,prov3,prov4,prov5,prov6,n,m,lag,oldvars,
      lagrangian,depvar,indepvar,symold,eqlold,rf,pv,gh,pold,gs:
global SADE,___cnm:
lagrangian:=args[1]:
depvar:=args[2]:
lagrangian:=convert(lagrangian,Diff):
gs:={}:
if type(depvar[1],function) then
   indepvar:={}:
   for i from 1 to nops(depvar) do
       lagrangian:=subs(depvar[i]=op(0,depvar[i]),lagrangian):
       indepvar:=indepvar union {op(depvar[i])}
   od:
   depvar:=map(x->op(0,x),depvar):
   indepvar:=convert(indepvar,list):
   if nargs=3 then
      gs:=args[3]
   fi
else
   indepvar:=args[3]:
   if nargs=4 then
      gs:=args[4]
   fi
fi:
SADE[forbiden]:={}:
SADE[_lag]:=lagrangian:
SADE[_depvar]:=depvar:
SADE[_indepvar]:=indepvar:
SADE[_vars]:=op(depvar):
SADE[_vars]:=SADE[_vars],op(indepvar):
SADE[dim]:=0:
n:=nops(indepvar):
m:=nops(depvar):
lag:=lagrangian:
for i from 1 to n do
for j from 1 to m do
    prov1:=op(j,depvar):
    prov1:=d||i||prov1:
    lag:=subs(eval(Diff(op(j,depvar),op(i,indepvar)))=prov1,lag)
od
od:
prov1:=0:
for i from 1 to n do
    prov1:=prov1+__eta||i(SADE[_vars])*diff(lag,op(i,indepvar))
od:
prov2:=0:
for i from 1 to m do
    prov2:=prov2+__xi||i(SADE[_vars])*diff(lag,op(i,depvar))
od:
prov3:=0:
for k from 1 to m do
for i from 1 to n do
    prov:=op(k,depvar):
    prov:=d||i||prov:
    prov3:=prov3+
       d_tot(__xi||k(SADE[_vars]),depvar,indepvar,i)*diff(lag,prov)
od
od:
prov4:=0:
for k from 1 to m do
for i from 1 to n do
for j from 1 to n do
    prov:=op(k,depvar):
    prov:=d||j||prov:
    provaux:=op(k,depvar):
    provaux:=d||i||provaux:
    prov4:=prov4+
         prov*d_tot(__eta||j(SADE[_vars]),depvar,indepvar,i)
         *diff(lag,provaux)
od
od
od:
prov4:=-prov4:
prov5:=0:
for i from 1 to n do
   prov5:=prov5+d_tot(__eta||i(SADE[_vars]),depvar,indepvar,i)
od:
prov5:=lag*prov5:
prov6:=0:
for i from 1 to n do
    prov6:=prov6-d_tot(c||i(SADE[_vars]),depvar,indepvar,i)
od:
SADE[eqlist]:={prov1+prov2+prov3+prov4+prov5+prov6}:
SADE[symlist]:=c1(SADE[_vars]):
for i from 2 to n do
    SADE[symlist]:=SADE[symlist],c||i(SADE[_vars])
od:
SADE[ccount]:=n+1:
for i from 1 to n do
    SADE[symlist]:=SADE[symlist],__eta||i(SADE[_vars])
od:
SADE[symlist]:=SADE[symlist],__xi1(SADE[_vars]):
for i from 2 to m do
    SADE[symlist]:=SADE[symlist],__xi||i(SADE[_vars])
od:
SADE[symlist]:=[SADE[symlist]]:
oldvars:=[SADE[_vars]]:
for i from 1 to n do
for j from 1 to m do
    prov:=op(j,depvar):
    prov:=d||i||prov:
    SADE[_vars]:=SADE[_vars],prov
od
od:
SADE[_vars]:=[SADE[_vars]]:
SADE[_system]:=[SADE[eqlist],SADE[symlist],{}]:
for i from 1 to n do
    replace(cat(__eta,i)=cat(c,SADE[ccount])):
    SADE[ccount]:=SADE[ccount]+1
od:
for i from 1 to m do
    replace(__xi||i=cat(c,SADE[ccount])):
    SADE[ccount]:=SADE[ccount]+1
od:
#SADE[_system]:=[subs(der=diff,SADE[eqlist]),SADE[symlist],{}]:
SADE[incognita]:={op(SADE[_system][2])}:
#SADE[var]:=SADE[_vars]:
SADE[fname]:=P:
SADE[fcount]:=1:
SADE[_decompvar]:=SADE[_vars]:
SADE[_system]:=subs(der=diff,SADE[_system]):
if gs<>{} then
   prov2:=expand(gs):
   for i from 1 to n do
       replace(SADE[_system][2][i+n]=coeff(prov2,D[indepvar[i]]))
   od:
   for i from 1 to m do
       replace(SADE[_system][2][i+2*n]=coeff(prov2,D[depvar[i]]))
   od
fi:
pold:=SADE[traceout]:
SADE[traceout]:=false:
prov2:=decompfnc():
while prov2 do prov2:=decompfnc() od:
SADE[traceout]:=pold:
#prov:=traperror(DEtools[rifsimp]([op(SADE[_system][1])],[op(SADE[incognita])])):
#if prov<>lasterror then
#   SADE[_system][1]:=map(x->op(1,x)-op(2,x),convert(prov[Solved],set))
#fi:
resolve():
if has({args},transformations) then
   RETURN(sym_generators())
fi:
#if SADE[_system][1]<>{} then RETURN({}) fi:
prov:=eval(noether_inv(lag,n,m,oldvars,depvar)):
for i from 1 to n do
for j from 1 to m do
    prov2:=op(j,depvar):
    prov2:=d||i||prov2:
    prov:=subs(prov2=Diff(op(j,depvar),op(i,indepvar)),prov)
od
od:
rf:={}:
prov3:=map(x->if type(x,symbol) then x else op(0,x) fi,SADE[incognita]):
for i from 1 to nops(prov) do
    prov2:=eval(prov[i]):
    pv:=setcont(prov2,SADE[incognita]):
    for j from 1 to nops(pv) do
    for k from 1 to nops(pv) do
        if j=k then
           prov2:=subs(pv[j]=1,prov2)
        else
           prov2:=subs(pv[k]=0,prov2)
        fi
    od
    od:
    prov1:=setcont(prov2,prov3):
    for k from 1 to nops(prov1) do
        prov2:=subs(prov1[k]=cat(_F,k),prov2)
    od:
    if not(type(prov2,list)) then prov2:=[prov2] fi:
    prov4:=map(x->expand(x)+gh,prov2):
    prov2:=map(x-> if type(x,numeric) then 0 else x fi,prov4[1])-gh:
    for k from 2 to nops(prov4) do
        prov2:=prov2,map(x-> if type(x,numeric) then 0 else x fi,prov4[k])-gh
    od:
    if nops(prov4)>1 then
       prov2:=[prov2]
    fi:
    if setcont(prov2,{depvar,indepvar})<>{} then
       rf:=rf union {expand(prov2)}
    fi
od:
if nops(indepvar)>1 then
   rf:=rf,indepvar
fi:
depvar:=args[2]:
rf:=[rf]:
for i from 1 to nops(depvar) do
    rf:=subs(op(0,depvar[i])=depvar[i],rf):
od:
rf:=convert(rf,diff):
rf:=op(rf):
rf
end:
# d_tot
# Rotina auxiliar de noether que calcula a derivada total de aa com relacao a` j-esima variavel dependente.
# Synopsis
# Parameters
# Description
# Rotina auxiliar de noether que calcula a derivada total de aa com relacao a` j-esima variavel dependente.
# Code
d_tot:=proc(aa,depvar,indepvar,j)
local i,prov,prov2:
prov:=0:
for i from 1 to nops(depvar) do
    prov2:=op(i,depvar):
    prov2:=d||j||prov2:
    prov:=prov+der(aa,op(i,depvar))*prov2
od:
prov:=prov+der(aa,op(j,indepvar)):
prov
end:
# noether_inv
# Rotina que calcula os invariantes de Noether a partir da solucao das simetrias.
# Synopsis
# Parameters
# Description
# Rotina que calcula os invariantes de Noether a partir da solucao das simetrias.
# Code
noether_inv:=proc(lag,n,m,oldvars,depvar)
local nnc,i,j,eqs,res,prov,ct:
global symlist,_ccc:
nnc:=nops(setcont(SADE[_system][2],SADE[incognita])):
res:={}:
ct:=setcont(SADE[_system][2],SADE[incognita]):
for i from 1 to nnc do
    eqs:=SADE[_system][2]:
    for j from 1 to nnc do
        if j<>i then
           eqs:=subs(op(j,ct)=0,eqs)
        else
           prov:=op(j,ct):
           eqs:=subs(prov=_ccc,eqs):
           eqs:=eval(eqs):
           eqs:=eval(subs(_ccc=prov,eqs))
        fi:
    od:
    res:=res union
         {simplify(nt_inv(lag,eqs,n,m,oldvars,depvar))}
od:
res
end:
# nt_inv
# Rotina auxiliar de noether_inv que calcula um invariante a partir de um dado gerador de simetria.
# Synopsis
# Parameters
# Description
# Rotina auxiliar de noether_inv que calcula um invariante a partir de um dado gerador de simetria.
# Code
nt_inv:=proc(lag,eqs,n,m,oldvars,depvar)
local res,i:
res:=nt_comp_inv(lag,eqs,n,m,1,oldvars,depvar):
for i from 2 to n do
    res:=res,nt_comp_inv(lag,eqs,n,m,i,oldvars,depvar)
od:
if n=1 then
   RETURN(res)
else
   RETURN([res])
fi:
end:
# nt_comp_inv
# Rotina auxiliar de nt_inv que calcula a i-esima componente do invariante de Noether.
# Synopsis
# Parameters
# Description
# Rotina auxiliar de nt_inv que calcula a i-esima componente do invariante de Noether.
# Code
nt_comp_inv:=proc(lag,eqs,n,m,i,oldvars,depvar)
local res,prov,prov2,prov3,k,l,gh:
prov:=op(oldvars):
res:=lag*__theta||i(prov):
for k from 1 to m do
    prov2:=op(k,depvar):
    prov2:=d||i||prov2:
    for l from 1 to n do
        prov3:=op(k,depvar):
        prov3:=d||l||prov3:
        res:=res+diff(lag,prov2)*(__eta||k(prov)-prov3*__theta||l(prov))
    od
od:
for k from 1 to n do
    res:=subs(__theta||k(prov)=op(k+n,eqs),res)
od:
for k from 1 to m do
    res:=subs(__eta||k(prov)=op(k+2*n,eqs),res):
od:
#for k from 1 to n do
#    res:=res-op(k,eqs)
#od:
res:=res-op(i,eqs):
res
end:
# polyn
#
# polyn([vars],[vdep],order) returns a polynomial in variables vars, of order order
# where the coefficients in the polynomial are functions of the remaining
# variables in vdep. polyn accepts a fouth argument even, which
# returns a polynomial with even powers
#
polyn:=proc()
local i1,i2,prov,prov2,vdep,flag,vard,order:
global SADE:
vard:=args[1]:
vdep:=args[2]:
order:=args[3]:
if nargs=4 and args[4]=`even` then flag:=1 else flag:=0 fi:
prov:=1:
for i1 from 1 to nops(vard) do
     prov2:=1:
     for i2 from 1 to order do
          prov2:=prov2+op(i1,vard)^i2
     od:
     prov:=prov*prov2
od:
prov:=expand(prov):
prov2:=0:
if vdep<>{} then
   vdep:=op(vdep):
   #varsdep:=vdep:
   for i1 from 1 to nops(prov) do
        if degree(op(i1,prov),vard)<=order then
           if (flag=1 and type(degree(op(i1,prov),vard),even)) or flag=0 then
             prov2:=prov2+cat(c,SADE[ccount])(vdep)*op(i1,prov):
             SADE[ccount]:=SADE[ccount]+1
           fi
        fi
   od
else
   for i1 from 1 to nops(prov) do
        if degree(op(i1,prov),vard)<=order then
           if (flag=1 and type(degree(op(i1,prov),vard),even)) or flag=0 then
             prov2:=prov2+cat(c,SADE[ccount])*op(i1,prov):
             SADE[ccount]:=SADE[ccount]+1
           fi
        fi
   od
fi:
prov2
end:
# twodim_cancoord
#
# Computes canonical coordinates for the generator G in the variables vars.
# The result is given as a substitution rule in the variables newvars.
#
twodim_cancoord:=proc(G,vars,newvars)
local n,p1,p2,r1,r2,u1,u2,e,unid,m:
#
# Aqui so definimos a funcao unitaria. Pode (e deve) ser generalizado.
#
m:=1:
unid:=proc(x) x^m end:
p1:=coeff(G,D[vars[1]]):
p2:=coeff(G,D[vars[2]]):
u1:=r1(op(vars)):
u2:=r2(op(vars)):
e:={p1*diff(u1,vars[1])+p2*diff(u1,vars[2])=0,
    p1*diff(u2,vars[1])+p2*diff(u2,vars[2])=1}:
e:=pdsolve(e,{u1,u2}):
n:=1:
#print(e):
while has(e,cat(_F,n)) do
      e:=eval(subs(cat(_F,n)=unid,e)):
      n:=n+1
od:
e:=subs(e,{newvars[1]=u1,newvars[2]=u2}):
e
end:
# indepord
#
# Returns the independent variables in descending ordering of derivative order.
#
indepord:=proc(eq,indep,dep,u)
local i,j,wd,t,r,p,d:
wd:=orddiff(whichder(eq),indep,dep):
wd:=map(x->if has(x,u) then x else 1 fi,wd):
wd:={op(wd)} minus {1}:
wd:=map(x->x[4],wd):
t:=array(1..nops(indep)):
for i from 1 to nops(indep) do
    t[i]:=max(op(map(x->x[i],wd)))
od:
r:=1:
for i from 1 to nops(indep) do
    p:=0:
    d:=-1:
    for j from 1 to nops(indep) do
        if t[j]>d then
           p:=j:
           d:=t[j]
        fi
    od:
    t[p]:=-10:
    r:=r,p
od:
r:=[r]:
r:=r[2..nops(r)]:
r:=map(x->indep[x],r):
r
end:
# regular_diff
#
# Returns those derivatives in eq which are not on the functions in u.
#
regular_diff:=proc(eq,u)
local i,drv,p:
p:=whichder(eq):
drv:={}:
for i from 1 to nops(p) do
    if setcont(p[i],u)={} then
#       ERROR(`Unable to handle differential equations with derivatives of unspecified functions.`)
       drv:=drv union {p[i]}
    fi
od:
drv
end:
# regularize_eq
#
# Returns a list with the first element with equations in eq regularized, i.e.  with all derivatives
# of fucntions not in vars replaced by pure funcions using the root name in nome. The second
# element gives the substitution rules to obtain the original form in eq.
#
regularize_eq:=proc(eq,vars,nome)
local res,dv,dd,eq2,regra,nn,pr,indep,dep,rr,nm,i,vars2:
dd:=regular_diff(eq,vars):
dv:=whichder(eq):
dv:=dv minus dd:
nn:=nops(dd):
vars2:={}:
for i from 1 to nops(dd) do
    pr:=dd[i]:
    while has(pr,diff) do pr:=op(1,pr) od:
    vars2:=vars2 union {pr}
od:
regra:={}:
eq2:=eq:
dep:={op(map(x->op(0,x),vars2))}:
indep:={op(map(x->op(x),vars2))}:
for i from 1 to nn do
    pr:=highestdiff(dd,indep,dep):
    dd:=dd minus {pr}:
    nm:=cat(nome,i):
    nm:=nm(op(setcont(pr,indep))):
    regra:=regra union {nm=pr}:
    eq2:=subs(pr=nm,eq2)
od:
[eq2,regra]
end:
# partial_involutive
#
# Reduces part of the determining system with equations with less than SADE[partial_reduction]
# term. The argument tp is rifs or janet, to use rifsimp or a Janet basis
# to reduce to the involutive form.
#
partial_involutive:=proc(tp)
local eqs,eqsrest,i,pr,unks,u2,v2:
global SADE:
if SADE[traceout]=true then
   print(``):
   print(`Trying to partially reduce the system to involutive form`)
fi:
if not(type(SADE[partial_reduction],constant)) then
   SADE[partial_reduction]:=5
fi:
pr:=SADE[_system][1]:
pr:=sizeorder(pr):
eqs:={}:
i:=1:
while i<=nops(pr) and nops(pr[i])<=SADE[partial_reduction] do
      eqs:=eqs union {pr[i]}:
      i:=i+1
od:
eqs:=simplify(eqs) minus {0}:
if eqs={} then
   RETURN(SADE[_system])
fi:
eqsrest:=pr[i..nops(pr)]:
unks:=setcont(eqs,SADE[incognita]):
eqs:=clean_eqs(eqs,unks):
if tp=rifs then
   eqs:=traperror(rifsimp(eqs,[op(unks)])):
   if eqs<>lasterror then
      eqs:=map(x->op(1,x)-op(2,x),eqs[Solved]):
      SADE[_system]:=[{op(eqs),op(eqsrest)},SADE[_system][2],SADE[_system][3]]:
   else
      if eqs="system is inconsistent" then
         ERROR(res)
      else
         if SADE[_partial_inv_first]<>false then
            v2:=SADE[_vars]:
            u2:=map(x->op(0,x),SADE[incognita]):
            pr:=traperror(KolchinRitt(SADE[_system][1],v2,u2,_purelex)):
            if pr<>lasterror then
               SADE[_system]:=[{op(pr)},SADE[_system][2],SADE[_system][3]]
            fi
         fi
      fi
   fi
fi:
#if tp=janet or eqs=lasterror then
if tp=janet then
   eqs:=traperror(Janet[JanetBasis]([op(eqs)],[unks],
                            map(x->op(0,x),unks))):
   if pr<>lasterror and type(eqs,list) then
      SADE[_system]:=[{op(eqs),op(eqsrest)},SADE[_system][2],SADE[_system][3]]
   else
      error(`Unable to partially reduce the determining system to the involutive form`)
   fi
fi:
if SADE[traceout]=true then
   print(`reduced...`):
   print(``)
fi:
SADE[_system]:
end:
# uniform_function
#
# Returns the expression in the argument with all the arguments of functions having the same name
# such that arguments with the same name appear in the correct same order.
# Ex: F(x,y) and F(y,x) are written both as F(x,y).
#
uniform_function:=proc(a)
local r,fs,p,p2,i,f2:
fs:=whichfunction(a):
r:=a:
while fs<>{} do
      p:=fs[1]:
      fs:=fs minus {p}:
      f2:=fs:
      for i from 1 to nops(fs) do
          p2:=fs[i]:
          if op(0,p)=op(0,p2) then
             r:=subs(p2=p,r):
             f2:=f2 minus {p2}
          fi
      od:
      fs:=f2
od:
r
end:
# whoisdiff
#
# Testes if the derivative in a is a derivative of the function name in v.
#
whoisdiff:=proc(a,v)
local r:
r:=a:
while has(r,diff) do
      r:=op(1,r)
od:
if op(0,r)=v or r=v then
   r:=true
else
   r:=false
fi:
r
end:
# suball
#
# Replaces the substitutions rules in reg involving derivatives and
# considering all possible implicit substititons.
#
suball:=proc(reg,eqs::set,depvars)
local r,i,dold,dnew,v,u:
r:=eqs:
if not(type(r[1],`=`)) then
   r:=map(x->x=0,r)
fi:
u:=[op(map(x->op(0,x),depvars))]:
v:=[op({op(map(x->op(x),depvars))})]:
dnew:=whichder(r):
while dnew<>dold do
      dold:=dnew:
      for i from 1 to nops(reg) do
          r:=subeq(reg[i],r,v,u)
      od:
      dnew:=whichder(r)
od:
r:=map(x->rhs(x)-lhs(x),r):
r
end:
# bestdiff
#
# Identifies which variables is the best one to consider for theta=1.
#
bestdiff:=proc(eqs,indep,dep)
local i,r,rdep,eqs2,tord,n:
eqs2:=[op(eqs)]:
tord:=map(x->lowestdiff_var(eqs2,x,indep),dep):
n:=-1:
for i from 1 to nops(tord) do
    if tord[i][2]> n then
       n:=tord[i][2]:
       r:=tord[i][1]:
       rdep:=tord[i][3]
    fi
od:
[r,rdep]
end:
# bestdiffvar
#
# Returns a list with the variables ordered according to the
# highest derivative with respect to each of them, from lowest to highest.
#
bestdiffvar:=proc(eqs,indep,dep)
local i,indep2,res,pr:
res:=1:
indep2:={op(indep)}:
for i from 1 to nops(indep) do
    pr:=[op(indep2)]:
    pr:=bestdiff(eqs,indep2,dep):
    pr:=pr[1]:
    res:=res,pr:
    indep2:=indep2 minus {pr}
od:
res:=[res]:
res:=res[2..nops(res)]:
res
end:
# comm
#
# Computes the commutator of two generators f and g in the variables vars (dependent and independent).
#
comm:=proc(f,g,vars)
local i,j,f2,g2,res,prov,prov2,pr,pr2,c1,c2,v1,v2:
global SADE,_gh,_gh2,_qwe:
f2:=expand(f):
g2:=expand(g):#print(f2,g2):
if type(f2,`+`) then
   res:=0:
   for i from 1 to nops(f2) do
       res:=res+comm(op(i,f2),g2,vars)
   od:
   RETURN(res)
fi:
if type(g2,`+`) then
   res:=0:
   for i from 1 to nops(g2) do
       res:=res+comm(f2,op(i,g2),vars)
   od:
   RETURN(res)
fi:
c1:=1:
c2:=1:
f2:=f2*_gh:
g2:=g2*_gh:
v1:={}:
v2:={}:
for i from 1 to nops(f2) do
    prov:=op(i,f2):
    if has(prov,D) then
       v1:=[op(prov)]
    else
       c1:=c1*prov
    fi
od:
for i from 1 to nops(g2) do
    prov:=op(i,g2):
    if has(prov,D) then
       v2:=[op(prov)]
    else
       c2:=c2*prov
    fi
od:
c1:=subs(_gh=1,c1):
c2:=subs(_gh=1,c2):
if nops(v1)>0 and nops(v2)>0 then
prov:=c1*diff(c2*diff(_qwe(op(vars)),op(v2)),
      op(1..nops(v1),v1))
     -c2*diff(c1*diff(_qwe(op(vars)),op(1..nops(v1),v1)),
      op(1..nops(v2),v2)):
prov:=eval(subs(_gh=1,prov)):
prov:=convert(expand(simplify(prov)),diff):
fi:
if nops(v1)=0 and nops(v2)=0 then RETURN(0) fi:
if nops(v1)=0 and nops(v2)>0 then
   RETURN(-comm(g2,f2,vars))
fi:
if nops(v1)>0 and nops(v2)=0 then
   prov:=expand(simplify(
         c1*diff(c2*_qwe(op(vars)),op(v1))
        -c2*c1*diff(_qwe(op(vars)),op(v1))))
fi:
prov:=subs(_gh=1,prov)+_gh2:
res:=0:
for i from 1 to nops(prov) do
    c1:=1:
    prov2:=op(i,prov)*_gh:
    for j from 1 to nops(prov2) do
        pr:=op(j,prov2):
        if has(pr,diff) and has(pr,_qwe) then
           pr2:=op(2..nops(pr),pr):
           pr:=op(1,pr):
           while has(pr,diff) do
                 pr2:=pr2,op(2..nops(pr),pr):
                 pr:=op(1,pr)
           od:
           c1:=c1*D[pr2]
        else
           c1:=c1*pr
        fi
    od:
    res:=res+c1
od:
res:=subs({_gh=1,_gh2=0,_qwe(op(vars))=1},res):
res
end:
# com_table
#
# Returns the commutator table of a set of differential generators as an array. The result is represented as
# a linear expansion in the generators represented by g||i. The inputs are: a-> a list of symmetry generators,
# var-> a set or list with the dependent and independet variable names and g-> a name to be used in the output
# to represent the generators.
#
com_table:=proc(a,v,g)
local res,i,j,k,p,r,n,l,l2,_a,unks,b,u1,u2,u3,pold:
global SADE:
u1:=SADE[_system]:
u2:=SADE[_vars]:
u3:=SADE[_decompvar]:
pold:=SADE[traceout]:
SADE[traceout]:=false:
if not(type(SADE[_decompvar],set)) and not(type(SADE[_decompvar],list)) then
   SADE[_decompvar]:={}
else
   SADE[_decompvar]:={op(SADE[_decompvar])}
end:
SADE[_decompvar]:=SADE[_decompvar] union {op(v)}:
SADE[_vars]:=SADE[_decompvar]:
#SADE[incognita]:={op(v)}:
SADE[incognita]:={}:
n:=nops(a):
res:=array(1..n,1..n,antisymmetric):
l:=0:
l2:=0:
unks:={}:
b:=map(x->D[x],v):
for i from 1 to n do
    l:=l+cat(_a,i)*a[i]:
    l2:=l2+cat(_a,i)*cat(g,i):
    SADE[incognita]:=SADE[incognita] union {cat(_a,i)}:
    unks:=unks union {cat(_a,i)}
od:
for i from 1 to n do
    res[i,i]:=0:
    for j from i+1 to n do
        p:=expand(comm(a[i],a[j],v)-l):
        p:={coeffs(p,b)}:
        SADE[_system]:=[p,{},{}]:
        decompfnc():
        p:=SADE[_system][1]:
        p:=tautoelim(solve(p,unks)):
        if setcont(p,v)<>{} or p={} then ERROR(`Not a closed set under commutation`) fi:
        r:=subs(p,l2):
        res[i,j]:=r
        #print(i,j,p)
    od
od:
SADE[_system]:=u1:
SADE[_vars]:=u2:
SADE[_decompvar]:=u3:
SADE[traceout]:=pold:
evalm(res)
end:
# StructConst
#
# Returns an array with the structure constants of the algebra defined
# by the generators in gens, with variables (dependent and independent)
# in vars.
#
StructConst:=proc(gens::list,vars::set)
local ng,ct,G,c,Cstruct,ceqs,i,j,k,pr,cvrs,gv:
ng:=nops(gens):
ct:=com_table(gens,vars,G):
ceqs:={}:
cvrs:={}:
gv:={}:
for i from 1 to ng do
    gv:=gv union {cat(G,i)}:
    for j from 1 to ng do
        pr:=0:
        for k from 1 to ng do
            pr:=pr+c(i,j,k)*cat(G,k):
            cvrs:=cvrs union {c(i,j,k)}
        od:
        pr:=ct[i,j]-pr:
        ceqs:=ceqs union {pr}
    od:
od:
ceqs:=map(x->coeffs(x,gv),ceqs):
ceqs:=solve(ceqs,cvrs):
Cstruct:=array(1..ng,1..ng,1..ng):
for i from 1 to nops(ceqs) do
    pr:=ceqs[i]:
    Cstruct[op(op(1,pr))]:=op(2,pr)
od:
eval(Cstruct)
end:
# AdjointRep
#
# Returns an array with the generators of the adjoint Representation.
# The first index corresponds to the adjoint vectro an the second indesx to
# the vectr at which it is calculated.
#
AdjointRep:=proc(gens::list,vars::set,G,x)
local i,j,k,res,ng,mt,stc,expm,pr,vg,vgmult:
ng:=nops(gens):
res:=array(1..ng,1..ng):
mt:=Matrix(ng):
stc:=StructConst(gens,vars):
for j from 1 to ng do
    for i from 1 to ng do
    for k from 1 to ng do
        mt[i,k]:=stc[i,j,k]
    od
    od:
    expm:=LinearAlgebra[MatrixExponential](mt,x):
    for i from 1 to ng do
        vg:=Matrix([[seq(0,k=1..ng)]]):
        vg[1,i]:=1:
        vgmult:=LinearAlgebra[MatrixMatrixMultiply](vg,expm):
        pr:=0:
        for k from 1 to ng do
            pr:=pr+vgmult[1,k]*cat(G,k):
        od:
        res[j,i]:=pr:
    od     
od:
evalm(res)
end:
# Implementation - Solution of Non-Linear Overdertermined PDEs
# nonlindsolve
#
# Tries to solve a non-linear system of overdetermined PDE's in syst and unknowns in unknowns.
#
nonlindsolve:=proc(syst,unknowns)
local i,k,vrs,r,eqs,unks,unk2,res,res2,_D,_G,cD,cG,nome,p,nn,
      s1,s2,u2,sol,sol2,fncs,cons,solution,fl,eqs2,eqs3,cc,unkopt:
global SADE,uuu:
SADE[_compatnoeqs]:={}:
eqs:=eval(syst):
unks:={op(unknowns)}:
if has({args},builtin) then
   unkopt:=unks,builtin
else
   unkopt:=unks
fi:
vrs:=map(x->op(x),unks):
#
# Defines the prefix name of new unknowns and set the counter for these variables.
#
if not(type(SADE[_nlfcount],integer)) then
   SADE[_nlfname]:=_p:
   SADE[_nlfcount]:=1
fi:
# Tests for a preliminary reduction to involutive form.
if has({args},involutive) then
    p:=traperror(timelimit(SADE[_timeinvol],rifsimp(eqs,[op(unknowns)],casesplit,checkempty))):
    if p=lasterror then
       if SADE[traceout]=true then
          print(`In reducing to involutive form: `,p):
          print(` `)
       fi:
       res:=nonlindsolve(eqs,unkopt):
       RETURN(res):
    else
       if type(p[casecount],integer) then
          if SADE[traceout]=true then
             print(`Creating new branch...`):
             print(` `)
          fi:
          res:={}:
          for i from 1 to p[casecount] do
              eqs2:=map(x->op(1,x)-op(2,x),p[i][Solved]):
              eqs2:=nonlindsolve(eqs2,unkopt):
              res:=res union eqs2
          od
       else
          eqs2:=map(x->op(1,x)-op(2,x),p[Solved]):
          res:=nonlindsolve(eqs2,unkopt):
       fi:
       RETURN(res)
    fi
else
   if has({args},builtin) then
      res:={pdsolve(syst,unks)}:
      if res<>{} then
         res:=map(x->if type(x,list) then 0 else x fi,res) minus {0}
      fi:
      if res={} then
         res:={[map(x->x=x,unks),{syst}]}:
         RETURN(res)
      fi:
      res:=map(x->[x,{}],res):
      RETURN(res)
   fi:
   res:=[op(unks)]:
   res2:=res:
#
# Decomposes equations which are expansions in LI functions.
#
   r:=nonlinli(eqs,unks,vrs):
   if r<>false then
      eqs:=r
   fi:
   eqs:=eval(eqs):
#
# Solves all possible linear equations.
#
   r:=solvlinsyst(eqs,unks):
#
# Tracks all arbitrary constants and functions in the solution of linear equations.
#
   if r<>false then
      eqs:=r[1]:
      unks:=unks minus map(x->op(1,x),r[2]) union r[3]:
      res2:=subs(r[2],res2)
   fi:
   i:=1:
   cD:=0:
   while has(eqs,cat(_C,i)) or has(res2,cat(_C,i)) do
         cD:=cD+1:
         eqs:=subs(cat(_C,i),cat(_D,i),eqs):
         res2:=subs(cat(_C,i),cat(_D,i),res2):
         unks:=unks union {cat(_D,i)}:
         i:=i+1
   od:
   i:=1:
   cG:=0:
   while has(eqs,cat(_F,i)) or has(res2,cat(_F,i)) do
         cG:=cG+1:
         eqs:=subs(cat(_F,i),cat(_G,i),eqs):
         res2:=subs(cat(_F,i),cat(_G,i),res2):
         nome:=traperror(searchfunction(cat(_G,i),eqs)):
         if nome=lasterror then
            nome:=searchfunction(cat(_G,i),res2)
         fi:
         unks:=unks union {nome}:
         i:=i+1
   od:
#
# Decomposes equations which are expansions in LI functions.
#
   r:=nonlinli(eqs,unks,vrs):
   if r<>false then
      eqs:=r
   fi:
   eqs:=eval(eqs):
fi:
sol2:={}:
fncs:={}:
if eqs<>{} then
#
# Reduces to the involutive form with cases.
#
   if SADE[traceout]=true then
      print(``):
      print(`Preliminary reduction to the involutive form....`):
      print(``):
   fi:
   if not(type(SADE[partial_reduction],constant)) then
      SADE[partial_reduction]:=5
   fi:
   eqs:=sizeorder(eqs):
   i:=1:
   eqs2:={}:
   while nops(eqs[1])<SADE[partial_reduction] and i<=nops(eqs) do
         eqs2:=eqs2 union {eqs[i]}:
         i:=i+1
   od:
   eqs3:={op(eqs)} minus {eqs2}:
   unk2:=[op(setcont(eqs2,unks))]:
   p:=traperror(timelimit(SADE[_timeinvol],rifsimp(eqs2,unk2,casesplit,checkempty))):
   if p[status]="system is inconsistent" then
      RETURN({})
   fi:
   if p=lasterror or nops(eqs2)=0 then
      if SADE[traceout]=true then
         print(`Unable do reduce`):
         if eqs2<>{} then
            print(p):
            print(``)
         fi
      fi:
      fl:=false:
   else
      fl:=true:
      if SADE[traceout]=true then
         if type(p[casecount],integer) then
            cc:=p[casecount]
         else
            cc:=1
         fi:
         print(`Reduced with`,cc,`case(s)`):
         print(``)
      fi
   fi:
   nn:=p[casecount]:
   if not(type(nn,constant)) then nn:=1 fi:
#
# Solves each case separetelly.
#
   for i from 1 to nn do
       if SADE[traceout]=true then
          print(``):
          print(``):
          print(`===== Solving case`,i,` =====`):
          print(``):
          print(``)
       fi:
       if nn=1 then
          if fl then
             s1:=p[Solved]:
             cons:=p[Constraint]
          else
             s1:=map(x->x=0,eqs)
          fi
       else
          s1:=p[i][Solved]:
          cons:=p[i][Constraint]
       fi:
       if type(cons,list) then
          cons:={op(cons)}:
          cons:=map(x->op(1,x)-op(2,x),cons)
       else
          cons:={}
       fi:
       s1:=map(x->op(1,x)-op(2,x),s1):
       s1:={op(s1)} union cons:
       u2:=setcont(s1,unks):
       s1:=s1 union eqs3:
#
# Solves the current case
#
       s2:=gennlsolve(s1,u2,vrs,1):
#
#
       for k from 1 to nops(s2) do
           sol:=s2[k]:
           sol2:=sol2 union {[sol[2],simplify(sol[1]) minus {0}]}:
           fncs:=fncs union sol[3]
       od
   od
else
   sol:=res[1]=res2[1]:
   for i from 2 to nops(res) do
       sol:=sol,res[i]=res2[i]
   od:
   sol:={[{sol},{}]}:
   sol2:=sol2 union sol
fi:
fncs:=fncs minus {op(unknowns)}:
fncs:=map(x->if type(x,function) then x else 0 fi,fncs):
fncs:=fncs minus {0}:
for i from 1 to SADE[_nlfcount] do
    p:=cat(SADE[_nlfname],i):
    if has(sol2,p) then
       p:=searchfunction(sol2,p):
       fncs:=fncs union {p}
    fi
od:
solution:={}:
for i from 1 to nops(sol2) do
    p:=simplify(eval(subs(sol2[i][1],res2))):
    p:={seq(res[i]=p[i],i=1..nops(res))}:
    p:=[p,sol2[i][2]]:
    solution:=solution union {p}
od:
k:=1:
for i from 1 to nops(fncs) do
    if has(solution,fncs[i]) then
       if type(fncs[i],function) then
          sol2:=subs(op(0,fncs[i])=cat(_F,k),solution)
       else
          sol2:=subs(fncs[i]=cat(_C,k),solution)
       fi:
       k:=k+1
    fi
od:
solution:=eval(solution):
solution
end:
# solvlinsyst
#
# Solves all linear equations in syst with unknowns unks. Returns a list
# with the new system as first element and the solutions
# of the linear equations as second element.
#
solvlinsyst:=proc(syst,unks)
local res,eqs,i,eqlin,nonlin,nome,newunks,pr:
global SADE:
eqs:=expand(syst):
eqlin:={}:
nonlin:={}:
for i from 1 to nops(eqs) do
    if iseqlin(eqs[i],unks) then
       eqlin:=eqlin union {eqs[i]}
    else
       nonlin:=nonlin union {eqs[i]}
    fi
od:
if eqlin={} then RETURN(false) fi:
res:=lindsolve(eqlin,unks,SADE[_vars]):
if res=false or res={} then RETURN(false) fi:
if type(res,list) then
   nonlin:=nonlin union res[2]:
   res:=res[1]
fi:
res:=tautoelim(res):
if res<>{} then
   pr:=traperror(expand(eval(subs(res,nonlin)))):
   if pr=lasterror then
      res:={}
   else
      nonlin:=pr
   fi
fi:
nonlin:=nonlin minus {0}:
if res={} then
   res:=false
else
   res:=[nonlin,res]
fi:
newunks:={}:
i:=1:
while has(res,cat(_C,i)) do
      nome:=cat(SADE[_nlfname],SADE[_nlfcount]):
      res:=subs(cat(_C,i)=nome,res):
      SADE[_nlfcount]:=SADE[_nlfcount]+1:
      newunks:=newunks union {nome}:
      i:=i+1
od:
i:=1:
while has(res,cat(_F,i)) do
      nome:=cat(SADE[_nlfname],SADE[_nlfcount]):
      res:=subs(cat(_F,i)=nome,res):
      SADE[_nlfcount]:=SADE[_nlfcount]+1:
      nome:=searchfunction(res,nome):
      newunks:=newunks union {nome}:
      i:=i+1
od:
if res=false then
   res:=false
else
   res:=[res[1],res[2],newunks]
fi:
res
end:
# nonlinli
#
# Tries to decompose every equation in system in the coefficient of L.I. functions, in the variables in vrs.
#
nonlinli:=proc(system,unks,vrs)
local i,j,p,p2,p3,flag,flag2,flag3,res,sist,seq:
global SADE:
sist:=system:
flag:=true:
SADE[incognita]:=unks:
SADE[_decompvar]:=vrs:
flag3:=false:
while flag do
      flag:=false:
      p:={}:
      p2:={}:
      for i from 1 to nops(sist) do
          j:=1:
          flag2:=true:
          while j<=nops(vrs) and flag2 do
                seq:=expand(sist[i]):
                p3:=traperror(timelimit(SADE[_timel],lifdec(seq,vrs[j]))):
                j:=j+1:
                if p3<>lasterror and p3[2]<>{} and setcont(p3[2],un)={} then
                   flag3:=true:
                   p:=p union p3[1]:
                   p2:=p2 union {sist[i]}:
                   flag2:=false:
                   flag:=true:
                   if SADE[traceout]=true then
                      print(``):
                      print(`Decomposing the equation`):
                      print(seq):
                      print(`as coefficient of the L.I. functions:`,op(p3[2])):
                      print(`into the new equations:`):
                      print(op(p3[1])):
                      print(``)
                   fi
                fi
          od
      od:
      if p<>{} then
         sist:=sist minus p2:
         sist:=sist union p:
         sist:=sist minus {0}
      fi
od:
if flag3 then
   res:=sist
else
   res:=false
fi:
res
end:
# singlelinsolve
#
# Tries to solve an algebraic equation which is linear in one of the unknowns
#
singlelinsolve:=proc(syst,unks)
local r,i,j,p,p2,eqs,wd,s1,s2:
#print(single,1111111111111111111):
eqs:=sizeorder({op(expand(syst))} minus {0}):
#print(single,2222222222222222222222222):
for i from 1 to nops(eqs) do
    p:=expand(eqs[i]):
    wd:=whichder(p):
    s2:={map(x->op(x),unks)}:
    for j from 1 to nops(unks) do
        p2:=unks[j]:
        s1:={op(p2)}:
        if traperror(degree(p,p2))=1 and not(has(wd,p2)) and s2 minus s1={} then
           r:=solve(p,{p2}):
           eqs:={op(expand(eval(subs(r,eqs))))} minus {0}:
           if SADE[traceout]=true then
              print(``):
              print(`Solving the linear algebraic equation:`):
              print(p):
              print(`with solution`):
              print(op(r)):
              print(``):
           fi:
           RETURN([eqs,r])
        fi
    od
od:
#print(single,9999999999999999999999999):
false
end:
# nonlinodesolve
#
# Tries to solve a single non-linear ODE in syst in one unknown in unks.
#
nonlinodesolve:=proc(syst,unks)
local res,res2,p,i,j,k,l,eqs,n,sol,sol2,funcs,nome,newunks,eqs2,mum,vrs:
global SADE:
vrs:={op(map(x->if type(x,function) then op(x) else 0 fi,unks))} minus {0}:
mum:=x->1:
eqs:=expand(syst) minus {0}:
eqs:=sizeorder(eqs):
if nargs=3 then
   n:=args[3]
else
   n:=100000
fi:
i:=1:
if not(type(SADE[timelim],constant)) then
   SADE[timelim]:=-1
fi:
if SADE[traceout]=true then
   print():
   print(`Trying to solve a non-linear equation with at most`,n,`terms`):
   print()
fi:
while i<=nops(eqs) and nops(eqs[i])<=n do
    sol:=nonlinsolveeq(eqs[i],unks,vrs):
    if sol<>false then
       k:=1:
       newunks:={}:
       while has(sol,cat(_C,k)) do
             nome:=cat(SADE[_nlfname],SADE[_nlfcount]):
             SADE[_nlfcount]:=SADE[_nlfcount]+1:
             sol:=subs(cat(_C,k)=nome,sol):
             newunks:=newunks union {nome}:
             k:=k+1
       od:
       k:=1:
       while has(sol,cat(_F,k)) do
             nome:=cat(SADE[_nlfname],SADE[_nlfcount]):
             SADE[_nlfcount]:=SADE[_nlfcount]+1:
             sol:=subs(cat(_F,k)=nome,sol):
             nome:=searchfunction(sol,nome):
             newunks:=newunks union {nome}:
             k:=k+1
       od:
       if SADE[traceout]=true then
          print(``):
          print(`Solving the non-linear equation:`):
          print(eqs[i]):
          print(`with solution(s):`):
          print(op(sol)):
       fi:
       res2:={}:
       for k from 1 to nops(sol) do
           if SADE[_nlsimplify]=true then
              eqs2:=traperror(simplify(eval(subs(sol[k],eqs))))
           else
              eqs2:=traperror(eval(subs(sol[k],eqs)))
           fi:
           eqs2:=eval(subs(csgn=mum,signum=mum,abs=mum,eqs2)):
           if eqs2<>lasterror then
              eqs2:={op(eqs2)} minus {0}:
              sol2:=sol[k]:
              if not(type(sol2,set)) then
                 sol2:={sol2}
              fi:
              sol2:=map(x->if op(1,x)=op(2,x) then 0 else x fi,sol2) minus {0}:
              res2:=res2 union {[eqs2,sol2,newunks]}
           fi:
       od:
       RETURN(res2)
    fi:
    i:=i+1
od:
false
end:
# genlinsolve
#
# Aplies some solving routines to equations in syst, in the unknowns in unknowns and with variables in vrs.
#
genlinsolve:=proc(syst,unknowns,vrs)
local flag,flag2,r,eqs,eqs2,unks,res,res2,ne,kkk,nold,wd:
global SADE:
eqs:=syst:
unks:={op(unknowns)}:
#########################################
flag:=true:
flag2:=false:
res:=[op(unks)]:
res2:=res:
ne:=3:
kkk:=0:
while flag and kkk<20 do
      kkk:=kkk+1:
      flag:=false:
#
# Decomposes equations which are expansions in L.I. functions.
#
      r:=nonlinli(eqs,unks,vrs):
      if r<>false then
         eqs:=r:
         flag2:=true
      fi:
#
# Solves all linear equations
#
      r:=solvlinsyst(eqs,unks):
      if r<>false then
         flag:=true:
         eqs:=r[1]:
         unks:=unks minus map(x->op(1,x),r[2]) union r[3]:
         res2:=subs(r[2],res2)
      fi:
#
# Solves a single algebraic equation
#
      r:=singlelinsolve(eqs,unks):
      if r<>false then
         flag:=true:
         eqs:=r[1]:
         res2:=subs(r[2],res2)
      fi:
      if flag then flag2:=true fi:
      eqs:=map(x->numer(x),eqs):
od:
eqs:=eqs minus {0}:
if eqs<>{} then
   if SADE[traceout]=true then
      print(``):
      print(`Reducing the nonlinear system to the involutive form....`):
   fi:
   eqs:=map(x->numer(x),{op(eqs)}) minus {0}:
   nold:=eqs:
#
# Reduces the remaining equations (nonlinear) to the reduced involutive form.
#
   wd:=whichder(eqs):
   wd:=setcont(wd,unks):
   if wd<>{} then
      eqs2:=traperror(timelimit(SADE[_timeinvol],rifsimp(eqs,[op(setcont(eqs,unks))]))):
      if eqs2=lasterror then
         if SADE[traceout]=true then
            print(`Unable to reduce:`):
            print(eqs2):
            print(``)
         fi:
      else
         if SADE[traceout]=true then
            print(`System reduced....`):
            print(``):
         fi:
         if type(eqs2[Solved],list) then
            eqs:=eqs2[Solved]:
            eqs:=map(x->op(1,x)-op(2,x),eqs):
            eqs:=map(x->numer(x),{op(eqs)}):
         else
            if type(eqs2[Constraint],list) then
               eqs:=eqs2[Constraint]:
               eqs:=map(x->op(1,x)-op(2,x),eqs):
               eqs:=map(x->numer(x),{op(eqs)}):
            else
               eqs:={}:
            fi
         fi
      fi
   fi:
#
# Decomposes equations which are expansions in L.I. functions.
#
   r:=nonlinli(eqs,unks,vrs):
   if r<>false then
      eqs:=r
   fi:
   if eqs<>nold then
      flag2:=true
   fi
else
   flag2:=true
fi:
res:={seq(res[i]=res2[i],i=1..nops(res))}:
[res,eqs,unks,flag2]
end:
# gennlsolve
#
# Solves linear equations first and then non-linear equations.
#
gennlsolve:=proc(syst,unknowns,vrs)
local i,j,k,eqs,r,unks,unks2,res,res2,res3,ne,p,p2,p3,eqparam,l1,l2,old:
global SADE:
unks:=unknowns:
# In case it is called for the first time, by nolindsolve, equations
# are already in the correct form.
if nargs=4 then
   eqs:={}:
   for i from 1 to nops(syst) do
       p2:=[op(setcont(syst[i],unks))]:
       p:=traperror(timelimit(SADE[_timeinvol],rifsimp({syst[i]},p2))):
       if p<>lasterror then
          p:=traperror({op(map(x->op(1,x)-op(2,x),p[Solved]))}):
          if p<>lasterror then
             eqs:=eqs union p
          else
             eqs:=eqs union {syst[i]}
          fi
       else
          eqs:=eqs union {syst[i]}:
       fi:
   od
else
   eqs:=syst
fi:
res:=[op(unknowns)]:
res2:=res:
res3:={}:
ne:=SADE[_ne]:
#
# Solves all linear equations.
#
eqparam:=map(x->if setcont(x,unks)={} then x else 0 fi,eqs) minus {0}:
l1:=eqs minus eqparam:
l2:=setcont(eqs,unks):
r:=genlinsolve(l1,l2,vrs):
eqs:=r[2] union eqparam:
if r[4] then
#   eqs:=r[2] union eqparam:
   unks:=unks union r[3]:
   res2:=subs(r[1],res2)
fi:
#
# Tries to solve a single nonlinear ODE.
#
r:=nonlinodesolve(eqs,unks,ne):
if r<>false then
   old:=eqs:
# Considers each solution and creates a new branch.
   if SADE[traceout]=true and nops(r)>1 then
      print(`Creating new branch...`):
      print(` `)
   fi:
   for i from 1 to nops(r) do
       eqs:=r[i][1]:
       p3:=r[i][2]:
       p3:=map(x->if op(1,x)=op(2,x) then 0 else x fi,p3) minus {0}:
       unks2:=unks minus map(x->op(1,x),p3) union r[i][3]:
       p2:=subs(r[i][2],res2):
       eqs:=simplify(eqs minus {0}):
       if eqs={} then
          if p3<>lasterror then
             res3:=res3 union {[{},p2,unks2]}
          fi
       else
          p3:=map(x->setcont(x,unks2),eqs):
          if not(has(p3,{})) and p3<>{} then
             p:=gennlsolve(eqs,unks2,vrs):
             for k from 1 to nops(p) do
                 p3:=traperror(subs(p[k][2],p2)):
                 if p3<>lasterror then
                    res3:=res3 union {[p[k][1],p3,unks2 union p[k][3]]}
                 fi
             od
          fi
       fi
   od:
else
   res3:={[eqs,res2,unks]}
fi:
p:={}:
for k from 1 to nops(res3) do
    p2:={seq(res[i]=res3[k][2][i],i=1..nops(res))}:
    p2:=map(x->if op(1,x)=op(2,x) then 0 else x fi,p2) minus {0}:
    p:=p union {[res3[k][1],p2,res3[k][3]]}
od:
p:=simplify(p):
# Testar as solucoes para consistencia.
p
end:
# nldsolve
#
# Tries to solve a non-linear system of overdetermined PDE's in syst and unknowns in unknowns.
#
nldsolve:=proc(syst,unknowns)
local i,j,k,vrs,r,eqs,unks,unk2,res,res2,_D,_G,cD,cG,nome,p,nn,s1,s2,u2,sol,sol2,
      fncs,cons,solution,fl,eqs2,p1,p2,ww,zz:
global SADE:
SADE[_compatnoeqs]:={}:
eqs:=eval(syst):
if type(eqs[1],`=`) then
   eqs:=map(x->op(1,x)-op(2,x),eqs)
fi:
unks:={op(unknowns)}:
vrs:=map(x->op(x),unks):
#########################################
#
# Defines the prefix name of new unknowns and set the counter for these variables.
#
SADE[_nlfname]:=_p:
SADE[_nlfcount]:=1:
#########################################
res:=[op(unks)]:
res2:=res:
# Tests for a preliminary reduction to involutive form.
if not(has({args},involutive)) then
#
# Decomposes equations which are expansions in LI functions.
#
   r:=nonlinli(eqs,unks,vrs):
   if r<>false then
      eqs:=r
   fi:
   eqs:=eval(eqs):
#
# Solves all possible linear equations.
#
   r:=solvlinsyst(eqs,unks):
#
# Tracks all arbitrary constants and functions in the solution of linear equations.
#
   if r<>false then
      eqs:=r[1]:
      unks:=unks minus map(x->op(1,x),r[2]) union r[3]:
      res2:=subs(r[2],res2)
   fi:
   i:=1:
   cD:=0:
   while has(eqs,cat(_C,i)) or has(res2,cat(_C,i)) do
         cD:=cD+1:
         eqs:=subs(cat(_C,i),cat(_D,i),eqs):
         res2:=subs(cat(_C,i),cat(_D,i),res2):
         unks:=unks union {cat(_D,i)}:
         i:=i+1
   od:
   i:=1:
   cG:=0:
   while has(eqs,cat(_F,i)) or has(res2,cat(_F,i)) do
         cG:=cG+1:
         eqs:=subs(cat(_F,i),cat(_G,i),eqs):
         res2:=subs(cat(_F,i),cat(_G,i),res2):
         nome:=traperror(searchfunction(cat(_G,i),eqs)):
         if nome=lasterror then
            nome:=searchfunction(cat(_G,i),res2)
         fi:
         unks:=unks union {nome}:
         i:=i+1
   od:
fi:
sol2:={}:
if eqs<>{} then
#
# Reduces to the involutive form with cases.
#
   if SADE[traceout]=true then
      print(``):
      print(`Preliminary reduction to the involutive form....`):
      print(``):
   fi:
   unk2:=[op(setcont(eqs,unks))]:
   p:=traperror(rifsimp(eqs,unk2,casesplit,checkempty)):
   nn:=traperror(p[casecount]):
   if p[status]="system is inconsistent" then
      if SADE[traceout]=true then
         print("system is inconsistent")
      fi:
      RETURN({})
   fi:
   if p=lasterror or type(p,string) then
      if SADE[traceout]=true then
         print(`Sorry, but the present algorithm cannot solve the equivalence system`):
         print(`due to the following error when reducing to the involutive form:`):
         print(p):
         print(``):
         print(`Stoping now!`):
         print(``):
         ERROR()
      else
         ERROR(p)
      fi
   fi:
   if not(type(nn,constant)) then nn:=1 fi:
   if p=lasterror then
      if SADE[traceout]=true then
         print(`Unable do reduce`):
         print(p):
         print(``)
      fi:
      fl:=false:
   else
      fl:=true:
      if SADE[traceout]=true then
         print(`Reduced with`,nn,`case(s)`):
         print(``)
      fi
   fi:
   if not(type(nn,constant)) then nn:=1 fi:
#
# Solves each case separetelly.
#
   for i from 1 to nn do
       if SADE[traceout]=true then
          print(``):
          print(``):
          print(`===== Solving case`,i,` =====`):
          print(``):
          print(``)
       fi:
       if nn=1 then
          if fl then
             s1:=p[Solved]:
             cons:=p[Constraint]
          else
             s1:=map(x->x=0,eqs)
          fi
       else
          s1:=p[i][Solved]
       fi:
       s1:=map(x->op(1,x)-op(2,x),s1):
       s1:={op(s1)}:
       u2:=setcont(s1,unks):
#
# Solves the current case
#
       if SADE[traceout]=true then
          print(` `):
          print(`Solving the system:`):
          print(` `):
          print(s1):
          print(` `)
       fi:
       s2:=traperror([pdsolve({op(s1),ww(zz)},{op(u2),ww(zz)})]):
       if SADE[traceout]=true then
          print(` `):
          if s2=lasterror then
             print(`and obtained the following error message: `):
             print(` `):
             print(s2):
             print(` `)
          else
             print(`With solution:`):
             print(` `):
             print(map(z->z minus {ww(zz)},s2)):
             print(` `)
          fi
       fi:
       if s2<>lasterror then
          for j from 1 to nops(s2) do
              if type(s2[j],list) then
                 p1:=subs(s2[j][1],res2):
                 p2:=s2[j][2]:
                 sol:=res[1]=p1[1]:
                 for k from 2 to nops(res) do
                     sol:=sol,res[k]=p1[k]
                 od:
                 sol:={[{sol},p2]}
               else
                 p1:=subs(s2[j],res2):
                 sol:=res[1]=p1[1]:
                 for k from 2 to nops(res) do
                     sol:=sol,res[k]=p1[k]
                 od:
                 sol:={[{sol},{}]}
               fi:
               sol2:=sol2 union sol
          od
       fi:
   od
else
   sol:=res[1]=res2[1]:
   for i from 2 to nops(res) do
       sol:=sol,res[i]=res2[i]
   od:
   sol:={[{sol},{}]}:
   sol2:=sol2 union sol
fi:
fncs:={}:
for i from 1 to SADE[_nlfcount] do
    p:=cat(SADE[_nlfname],i):
    if has(sol2,p) then
       p:=searchfunction(sol2,p):
       fncs:=fncs union {p}
    fi
od:
solution:=sol2:
k:=1:
while has(solution,cat(_F,k)) do
      k:=k+1
od:
for i from 1 to nops(fncs) do
    if has(solution,fncs[i]) then
       if type(fncs[i],function) then
          solution:=subs(op(0,fncs[i])=cat(_F,k),solution)
       else
          solution:=subs(fncs[i]=cat(_C,k),solution)
       fi:
       k:=k+1
    fi
od:
solution:=eval(solution):
solution
end:
# nlalgdiff
#
# Tries to solve a single algebraic equation involving derivatives.
#
nlalgdiff:=proc(syst,unks)
local eq,i,j,p,p2,pd,r,syst2,res,vr:
vr:={}:
for i from 1 to nops(unks) do
    if type(unks[i],function) then
        vr:=vr union {op(unks[i])}
    fi
od:
syst2:=syst:
for i from 1 to nops(syst) do
    eq:=syst2[i]:
    p:=setcont(eq,unks):
    pd:=whichder(eq):
    pd:=setcont(pd,unks):
    p:=p minus pd:
    if p<>{} then
       eq:=simplify(eq):
       if eq=0 then p:={} fi
    fi:
    if p<>{} then
       r:=traperror({solve(eq,p)}):
       if r=lasterror or r={} then RETURN(false) fi:
       r:=map(x->tautoelim(x),r):
       #if type(r[1],set) and nops(r)=1 then r:=r[1] fi:
       res:={}:
       for i from 1 to nops(r) do
           p2:=r[i]:
           if not(type(p,set)) then
              p2:={p2}
           fi:
           p2:=map(x->if setcont(op(2,x),vr) minus setcont(op(1,x),vr)={}
                      then true else false fi,p2):
           if has(p2,false) then RETURN(false) fi:
           res:=res union {[r[i],{eq}]}
       od:
       RETURN(res)
    fi
od:
false
end:
# nonlinsolveeq
#
# Solves non-linear ODES and algebraic equations. The output
# is a list of all possible solutions obtained by dsolve or false
# if no solution is obtained. Each solution is a set of substitution
# rules.
# eq-> equation to be solved. unks-> unknow functions or constants.
#
nonlinsolveeq:=proc(eq,unks,vrs)
local i,sol,p,funcs,wd,te:
global SADE:
if nops(unks)>1 then
   sol:={}:
   for i from 1 to nops(unks) do
       if setcont(eq,{unks[i]})<>{} then
          p:=nonlinsolveeq(eq,{unks[i]},vrs):
          if p<>false then
             sol:=sol union p
          fi
       fi
   od:
   if sol={} then
      RETURN(false)
   else
      RETURN(sol)
   fi
fi:
p:=numer(eq):
funcs:=setcont(p,unks):
if setcont(p,vrs) minus map(x->op(x),funcs)<>{} then
   RETURN(false)
fi:
wd:=whichder(p):
wd:=map(x->if setcont(x,unks)={} then 0 else x fi,wd) minus {0}:
if setcont(wd,funcs)={} then
   sol:=traperror(timelimit(SADE[timelim],solve(p,{funcs[1]}))):
   if {sol}={} or sol={} or sol=lasterror then
      RETURN(false)
   fi:
   sol:={sol}
else
   sol:=traperror(timelimit(SADE[timelim],dsolve(p,funcs[1]))):
   if {sol}={} or sol={} or sol=lasterror then
      RETURN(false)
   fi:
   sol:={sol}:
   if type(sol[1],list) then
      sol:={op(op(sol))}
   fi
fi:
if {sol}={} or sol={} or {sol}=lasterror then
   RETURN(false)
fi:
if has({sol},int) or has({sol},Int) or has({sol},Intat) or
   has({sol},PDESolStruc) or has({sol},DESol) or has({sol},Intat)
then
   RETURN(false)
fi:
if type(sol,list) then
   sol:=op(sol)
fi:
te:=map(x->map(z->map(y->op(1,y),z),x),sol):
if has(te,diff) then
   RETURN(false)
fi:
sol
end:
# Implementation - PDE SOLUTIONS
# PDEreduction
#
# Obtaines the reductions of a (system of) PDE(s) from symmetry generators.
#
PDEreduction:=proc(eqs,funcs,gens)
local res:
if has([args],generic_solution) then
   RETURN(invariant_sol(eqs,funcs,gens,gensol))
fi:
invariant_sol(eqs,funcs,gens,pde_reduction)
end:
# charcrt
#
# Obtains the characteristic equations associated to the infinitesimal
# generator of transformation g. u is a list with the dependent variables and
# v a list with the dependent variables.
#
charcrt:=proc(g,unks,v)
local eqs,i,j,gen,p,u,r:
gen:=expand(g):
u:=map(x->op(0,x),unks):
r:={}:
for i from 1 to nops(unks) do
    r:=r union {u[i]=unks[i]}:
od:
eqs:={}:
for i from 1 to nops(u) do
    p:=subs(r,coeff(gen,D[u[i]])):
    for j from 1 to nops(v) do
        p:=p-diff(unks[i],v[j])*subs(r,coeff(gen,D[v[j]]))
    od:
    eqs:=eqs union {p}
od:
eqs
end:
# whichFarg
whichFarg:=proc()
global _Fvar:
_Fvar:=seq(args[i],i=1..nargs)
end:
# invariant_sol
#
# Obtains the invariant solution of the equations in eqs associated
# to a given set of symmetry generators gs, with unknowns in the list unk.
# The output is a set of solutions. If an explicit expression is not possible
# for a given solution, then it is given in the form of a list with substituion rules.
# If the solution of the characteristic equation involves terms with Intat or Int
# then the routine tries to particularize this solution in such a way that these terms vanish.
#
invariant_sol:=proc(eq2,unks::list,gs::set)
global _Fvar,SADE:
local i,j,k,ks,p,p2,p3,v,f,f2,fn,s,s2,s3,simvar,cv,cv2,res,res2,pr,eqs,solred,sd,_gh,nFmax,nFnm,fl,Fs:
nFmax:=200:
nFnm:={seq(cat(_F,i),i=1..nFmax)}:
SADE[_decompvar]:={op(map(x->op(x),unks))}:
eqs:=eq2:
if setcont(eqs,unks)<>{op(unks)} then
   f2:=true
else
   f2:=false
fi:
if f2 then
   SADE[_decompvar]:={op(map(x->op(x),unks))}
fi:
if not(type(eqs,set) or type(eqs,list)) then
   eqs:={eqs}
fi:
if type(eqs[1],`=`) then
   eqs:=map(x->op(1,x)-op(2,x),eqs)
fi:
v:={}:
for i from 1 to nops(unks) do
    v:=v union {op(unks[i])}
od:
v:=[op(v)]:
p:={}:
for i from 1 to nops(gs) do
    p:=p union charcrt(gs[i],unks,v)
od:
solred:=traperror(simplify({pdsolve(p,{op(unks)})})):
if solred={} then RETURN({}) fi:
##############################
fl:=true;
Fs:=map(x->cat(_F,x),{seq(i,i=1..100)}):
i:=1:
while fl do
      if nops(map(x->setcont(x,Fs),solred[i]))=nops(unks) then
         fl:=false:
         solred:=solred[i]
      else
         i:=i+1
      fi:
      if i>nops(solred) then RETURN({}) fi
od:
##############################
solred:={solred}:
if solred={} then RETURN({}) fi:
if type(op(1,[solred]),list) then RETURN({}) fi:
if solred=lasterror then RETURN({}) fi:
res:={}:
if has([args],gensol) then
   RETURN(solred)
fi:
for ks from 1 to nops(solred) do
    p:=solred[ks]:
    f:={}:
    i:=1:
    if not(has(p,RootOf)) then
    p:=regpds(p,v):
    f:=setcont(p,nFnm):
    if nops(f)<=nops(unks) then
       p:=regpds(p,v):
       if p<>{} then
       simvar:={}:
       fn:={}:
       for i from 1 to nops(f) do
           eval(subs(f[i]=whichFarg,p)):
           simvar:=simvar union {_Fvar}:
           fn:=fn union {f[i](_Fvar)}
       od:
       simvar:=simplify(simvar,symbolic):
       f:=fn:
       cv:={}:
       cv2:={}:
       for i from 1 to nops(simvar) do
           cv2:=cv2 union {simvar[i]=cat(xi,i)}
       od:
       cv:=newsolve(cv2,v):
       if {cv}={} or {cv}={{}} then RETURN({}) fi:
       p:=simplify(p,symbolic):
       s:=eqs:
       s:=expand(eval(subs(p,s))):
       for i from 1 to nops(cv) do
           s:=convert(simplify(subs(cv[i],s),symbolic),set) minus {0}:
           s:=simplify(convert(s,diff)):
           s:=map(x->numer(x),s):
       od:
       sd:=setcont(s,SADE[_decompvar]):
       s3:=s:
       SADE[_nolifdecindep]:=true:
       s:=simplify(expand(s)):
       for i from 1 to nops(sd) do
           s3:=traperror(op(map(x->if setcont(x,{sd[i]})={} then [{x},{}] else lifdec(x+_gh,sd[i]) fi,s))):
           if s3=lasterror then RETURN({}) fi:
           if s3<>{{}} and s3<>{} then
              s:=map(x->op(x[1]),{s3}):
              s:=subs(_gh=0,s) minus {0}
           fi:
       od:
       SADE[_nolifdecindep]:=false:
       pr:=f:
       for i from 1 to nops(cv) do
           pr:=simplify(subs(cv[i],pr),symbolic)
       od:
       if nargs>=4 and has({args},pde_reduction) then
          if simvar={} then
             res:=res union {[p,{},{}]}
          else
             pr:=xi1=simvar[1]:
             for j from 2 to nops(simvar) do
                 pr:=pr,cat(xi,j)=simvar[j]
             od:
             res:=res union {[p,s,{pr}]}
          fi
       else
          s2:=s:
          if nops(simvar)=1 then
             s:=traperror({dsolve(s,pr)})
          else
             s:=traperror({pdsolve(s,pr)})
          fi:
          if s={} or s=lasterror then
             s:={{}}
          fi:
          if not(type(s[1],list)) and s<>{{}} then
             s:={[op(s)]}
          fi:
          for j from 1 to nops(s) do
              if s={{}} or has(s[j],ODESolStruc) or has(s[j],RootOf) then
                 if s={{}} then s:={s2} fi:
                 if simvar<>{} then
                    pr:=xi1=simvar[1]:
                    for k from 2 to nops(simvar) do
                        pr:=pr,cat(xi,k)=simvar[k]
                    od:
                    res:=res union {[p,s[j],{pr}]}####################################
                 fi
              else
                 s2:=simplify(eval(subs(Int=int,s[j])),symbolic):
                 pr:=map(x->op(1,x[1]),s2):
                 if has(s2,Int) or has(pr,diff) or has(s2,DESol) then
                    pr:=xi1=simvar[1]:
                    for k from 2 to nops(simvar) do
                        pr:=pr,cat(xi,k)=simvar[k]
                    od:
                    res:=res union {[p,s2,pr]}
                 else
                    s2:=map(x->op(x),s2):
                    p3:=map(x->op(1,x),s2):
                    s2:=traperror(simplify(eval(subs(s2,s2)))):
                    if s2<>lasterror then
                       p2:=1:
                       for k from 1 to nops(s2) do
                           p2:=p2,p3[k]=op(2,s2[k])
                       od:
                       p2:=[p2]:
                       s2:=[op(2..nops(p2),p2)]:
                       for k from 1 to nops(simvar) do
                           s2:=subs(cat(xi,k)=simvar[k],s2)
                       od:
                       s2:=simplify(subs(s2,p)):
                       s2:=simplify(s2,symbolic):
                       res:=res union {s2}
                    fi
                 fi
              fi
          od
       fi
    fi
    fi
    fi
od:
p:=setcont(eq2,unks):
if res<>{} and p<>unks and type(res[1],set) then
   res2:=res:
   res:={}:
   for i from 1 to nops(res2) do
       p2:=map(x->if has(p,op(1,x)) then x else 0 fi,res2[i]) minus {0}:
       res:=res union {p2}
   od
fi:
res
end:
# newsolve
#
# Routine to avoid a bug in Maple17 solve 
#
newsolve:=proc(eqs,vars)
local i,res,v2:
res:=traperror(solve(eqs,vars)):
if res<>lasterror then RETURN(res) fi:
v2:=convert(map(z->convert(z,set),combinat[permute](vars,nops(eqs))),set):
for i from 1 to nops(v2) do
    res:=traperror(solve(eqs,v2[i])):
    if res<>lasterror and {res}<>{} and res<>{} then
       RETURN(res)
    fi
od:
false
end:
# regpds
#
# Tries to obtain a particular form of a solutions of the characteristic equation
# by equating to zero some arbitrary constant _Ci in such a way that no terms with
# Intat or Int are present in the final form.
#
regpds:=proc(s,v)
local r,s2,i,ghost,k,Cset,sol,pr:
r:=0:
s2:=expand(s):
s2:=op(2,s2[1])+ghost:
for i from 1 to nops(s2) do
    if has(op(i,s2),Intat) or has(op(i,s2),Int) then
       r:=r+op(i,s2)
    fi
od:
k:=1:
Cset:={}:
while has(r,cat(_C,k)) do
      Cset:=Cset union {cat(_C,k)}:
      k:=k+1
od:
k:=k-1:
r:=factor(r):
if not(type(r,`*`)) then RETURN(s) fi:
for i from 1 to nops(r) do
    pr:=op(i,r):
    if setcont(pr,v)={} and type(pr,name) and setcont(pr,Cset)<>{} then
       sol:={solve(pr=0,setcont(pr,Cset))}:
       if nops(sol)>1 then sol:=sol[1] fi:
       s2:=subs(sol,s):
       s2:=eval(subs(Intat=intat,Int=int,s2)):
       s2:=simplify(s2):
       RETURN(s2)
    fi
od:
s
end:
# sym_nonclassical
#
#  Computes nonclassical symmetries of a given system of differential equations.
#
sym_nonclassical:=proc(eqs,u::list,v::list)
local i,j,eqs2,eqsadded,p,se,ar,nm,s,s2,nc,tm:
global SADE:
SADE[_vars]:=[op(u),op(v)]:
if type(eqs,set) then
   eqs2:=eqs
else
   eqs2:={eqs}
fi:
if type(eqs2[1],`=`) then
   eqs2:=map(x->op(1,x)-op(2,x),eqs2)
fi:
se:={}:
ar:=op(map(x->x(op(v)),u)):
ar:=ar,op(v):
for i from 1 to nops(u) do
    nm:=cat(_eta,i):
    p:=nm(ar):
    for j from 1 to nops(v) do
        nm:=cat(_theta,j):
        p:=p-diff(u[i](op(v)),v[j])*nm(ar)
    od:
    se:=se union {p}
od:
eqsadded:=eqs2 union se:
symmetries(eqsadded,u,v):
for i from 1 to nops(u) do
    SADE[_system][1]:=subs(cat(_eta,i)=cat(eta,i),SADE[_system][1])
od:
for i from 1 to nops(v) do
    SADE[_system][1]:=subs(cat(_theta,i)=cat(theta,i),SADE[_system][1])
od:
SADE[_system][1]:=convert(SADE[_system][1],diff) minus {0}:
end:
# pdsolve_c
#
# Solves an overdetermined system of non-linear differential equations
# solving for a bug in maple routine pdsolve, used to solve the system,
# and putting the solutions using arbitrary constants labeled by _C.i
# (instead of using both _C.i and _c.i as in the usual output of pdsolve).
#
pdsolve_c:=proc(eqs2,vars)
local i,j,k,s,s2,s3,p,p2,r,r2,sol,_ccc,eqs,indeps:
eqs:=map(x->if type(x,`=`) then op(2,x)-op(1,x) else x fi,eqs2):
indeps:=map(x->op(x),vars):
s:={pdsolve(eqs,vars)}:
sol:={}:
for k from 1 to nops(s) do
    p:={}:
    i:=1:
    s2:=s[k]:
    while has(s2,_c[i]) do
          p:=p union {_c[i]}:
          i:=i+1:
    od:
    i:=1:
    while has(s2,cat(_C,i)) do
          p:=p union {cat(_C,i)}:
          i:=i+1:
    od:
    r:=simplify(eval(subs(s2,eqs))) minus {0}:
    if r<>{} then
       r:={solve(r,p)}:
       for j from 1 to nops(r) do
           s3:=simplify(subs(r[j],s2)):
           p2:=setcont(s3,p):
           r2:={}:
           for i from 1 to nops(p2) do
               s3:=subs(p2[i]=cat(_ccc,i),s3):
               r2:=r2 union {cat(_ccc,i)=cat(_C,i)}
           od:
           s3:=subs(r2,s3):
           sol:=sol union {simplify(s3)}
       od
    else
       p2:=setcont(s2,p):
       r2:={}:
       for i from 1 to nops(p2) do
           s2:=subs(p2[i]=cat(_ccc,i),s2):
           r2:=r2 union {cat(_ccc,i)=cat(_C,i)}
       od:
       s2:=subs(r2,s2):
       sol:=sol union {simplify(s2)}
    fi
od:
sol
end: 
# noncl_generators
#
# Solves a non-linear determining system using the maple routine pdsolve,
# and returns the corresponding infinitesimal transformation generators.
# Some solutions may be lost!!!
#
noncl_generators:=proc()
local s,t,s2,t2,i,j,n,m,r,r2,gens,gens2,p,ur,ds,gh,nn:
global SADE:
nn:=nops(SADE[_system][2]):
ur:=SADE[_system][2][nn]:
s:=eval(subs(ur=1,SADE[_system][1])):
t:=eval(subs(ur=0,SADE[_system][1])):
r:={}:
r2:={}:
if s<>{0} then
   s:=DEtools[rifsimp]([op(s)],SADE[_system][2][1..nn-1],casesplit):
   n:=s[casecount]
else
   n:=0:
   r:=r union {gh=gh}
fi:
if t<>{0} then
   t:=DEtools[rifsimp]([op(t)],SADE[_system][2][1..nn-1],casesplit):
   m:=t[casecount]
else
   m:=0:
   r:=r union {gh=gh}
fi:
if not(type(n,integer)) then n:=1 fi:
if not(type(m,integer)) then m:=1 fi:
for i from 1 to n do
    if n=1 then
       s2:=evalm(s)
    else
       s2:=s[i]
    fi:
    if not(has(s2[Case],"false split")) then
       s2:=convert(s2[Solved],set):
       s2:=map(x->op(1,x)-op(2,x),s2):
       s2:=nlpdsolve(s2,{op(SADE[_system][2])} minus {ur}):
       r:=r union s2
    fi
od:
for i from 1 to m do
    if m=1 then
       t2:=evalm(t):
    else
       t2:=t[i]
    fi:
    if not(has(t2[Case],"false split")) then
       t2:=convert(t2[Solved],set):
       t2:=map(x->op(1,x)-op(2,x),t2):
       t2:=nlpdsolve_c(t2,{op(SADE[_system][2])} minus {ur}):
       r2:=r2 union t2
    fi
od:
gens:={}:
for i from 1 to nops(r) do
    p:=eval(subs(ur=1,subs(r[i],SADE[_system][2]))):
    s:=0:
    for j from 1 to nops(SADE[_vars]) do
        s:=s+p[j]*D[SADE[_vars][j]]
    od:
    gens:=gens union {s}
od:
for i from 1 to nops(r2) do
    p:=eval(subs(ur=0,subs(r2[i],SADE[_system][2]))):
    s:=0:
    for j from 1 to nops(SADE[_vars]) do
        s:=s+p[j]*D[SADE[_vars][j]]
    od:
    gens:=gens union {s}
od:
i:=1:
while has(gens,cat(_F,i)) do
      gens:=subs(cat(_F,i)=cat(_G,i),gens)
od:
ds:=map(x->D[x],{op(SADE[_vars])}):
gens2:={}:
for i from 1 to nops(gens) do
    p:=factor(gens[i]):
    if type(p,`*`) then
       s:=1:
       for j from 1 to nops(p) do
           if setcont(op(j,p),ds)<>{} then
              s:=s*op(j,p)
           fi
       od:
       s:=collect(s,ds)
    else
       s:=p
    fi:
    gens2:=gens2 union {s}
od:
gens2
end:
# nlpdsolve
#
# Solves a non-linear overdetermined set of Patial Differential Equations.
# The input is given by the equation ser as the first argument and the unknown functions
# set as the second argument.
#
nlpdsolve:=proc(eqs,unks)
local i,r,p,eqsa,eqsb,eqs2,leq,l,flag,res1,res2,n,v,u2:
global SADE:
SADE[fcount]:=1:
SADE[incognita]:=unks:
u2:=unks:
v:=map(x->op(x),unks):
res1:=[op(unks)]:
res2:=res1:
eqsa:=eqs minus {0}:
flag:=true:
while flag and eqsa<>{} do
      for i from 1 to nops(unks) do
          eqsa:=eval(subs(unks[i]=unks[i]*l,eqsa))
      od:
      eqsb:={}:
      for i from 1 to nops(eqsa) do
          if degree(eqsa[i],l)=1 then
             eqsb:=eqsb union {eqsa[i]}
          fi
      od:
      eqsb:=subs(l=1,eqsb):
      eqsa:=subs(l=1,eqsa):
      eqsa:=eqsa minus eqsb:
      if eqsb={} then
         flag:=false
      else
         r:=lindsolve(eqsb,setcont(eqsb,SADE[incognita])):
         n:=1:
         while has(r,cat(_F,n)) do
               r:=subs(cat(_F,n)=cat(SADE[fname],SADE[fcount]),r):
               p:=searchfunction(r,cat(SADE[fname],SADE[fcount])):
               p:=setcont(p,v):
               u2:=u2 union {cat(SADE[fname],SADE[fcount])(op(p))}:
               SADE[fcount]:=SADE[fcount]+1:
               n:=n+1
         od:
         n:=1:
         while has(r,cat(_C,n)) do
               r:=subs(cat(_C,n)=cat(SADE[fname],SADE[fcount]),r):
               u2:=u2 union {cat(SADE[fname],SADE[fcount])}:
               SADE[fcount]:=SADE[fcount]+1:
               n:=n+1
         od:
         res2:=subs(r,res2):
         eqsa:=simplify(eval(subs(r,eqsa))) minus {0}:
         if SADE[traceout]=true then
            print(` `):
            print(`Reducing the system into the involutive form...`):
            print(` `):
         fi
      fi:
      eqsa:=DEtools[rifsimp](eqsa,[op(setcont(eqsb,u2))]):
      eqsa:={op(eqsa[Solved])}:
      eqsa:=map(x->op(1,x)-op(2,x),eqsa)
od:
r:=pdsolve_c(eqsa,setcont(eqsa,u2)):
r:=res1[1]=res2[1]:
for i from 2 to nops(res1) do
    r:=r,res1[i]=res2[i]
od:
r
end:
# twodim_cancoord
#
# Computes canonical coordinates for the generator G in the variables vars.
# The result is given as a substitution rule in the variables newvars.
#
twodim_cancoord:=proc(G,vars,newvars)
local n,p1,p2,r1,r2,u1,u2,e,unid,m:
#
# Aqui so definimos a funcao unitaria. Pode (e deve) ser generalizado.
#
m:=1:
unid:=proc(x) x^m end:
p1:=coeff(G,D[vars[1]]):
p2:=coeff(G,D[vars[2]]):
u1:=r1(op(vars)):
u2:=r2(op(vars)):
e:={p1*diff(u1,vars[1])+p2*diff(u1,vars[2])=0,
    p1*diff(u2,vars[1])+p2*diff(u2,vars[2])=1}:
e:=pdsolve(e,{u1,u2}):
n:=1:
#print(e):
while has(e,cat(_F,n)) do
      e:=eval(subs(cat(_F,n)=unid,e)):
      n:=n+1
od:
e:=subs(e,{newvars[1]=u1,newvars[2]=u2}):
e
end:
# pegaperm
#
# Returns a list of all lists of the form [i1,i2,...,ik], where each i1 ranges from 1 to n1,
# i2 from 1 to n2, and so on, , with l=[n1,n2,...,nk].
#
pegaperm:=proc(l)
local r,r2,i,j,k,p:
r:=[seq([i],i=1..l[1])]:
if nops(l)=1 then RETURN(r) fi:
for k from 2 to nops(l) do
    p:=[seq(i,i=1..l[k])]:
    r2:=[seq(seq([op(r[i]),p[j]],j=1..l[k]),i=1..nops(r))]:
    r:=r2
od:
r
end:
# umcomprox
#
# Puts the output of pdsolve in a usable format in subs.
#
umcomprox:=proc(a)
local l,p,q,q2,r,i,j,c:
if nops(a)=1 then RETURN(a) fi:
l:=map(x->nops(x),a):
l:=pegaperm(l):
r:={}:
for i from 1 to nops(l) do
    p:=1:
    for j from 1 to nops(l[i]) do
        p:=p,a[j][l[i][j]] 
    od:
    p:=[p]:
    p:=p[2..nops(p)]:
    r:=r union {p}
od:
r
end:
# umnosoutros
#
# Replaces the relations in rg one into the others.
#
umnosoutros:=proc(rg)
local i,p,r:
if type(rg[1],set) then
   r:=map(x->op(x),rg)
else
   r:=rg
fi:
r:=[op(r)]:
for i from 1 to nops(rg) do
    p:=[op(r[1..i-1]),op(r[i+1..nops(r)])]:
    p:=eval(subs(r[i],p)):
    r:=[op(p[1..i-1]),r[i],op(p[i..nops(r)-1])]
od:
r:={op(r)}
end:
# invariant_cond
#
# Obtains the invariant conditions for the unknwon functions in unks with respect to the generators in gs
# and satisfying equations in eq2.
#
invariant_cond:=proc(unks::list,gs::set)
global _Fvar,SADE:
local i,p,v,f,f2,fn,res,res2,pr:
SADE[_decompvar]:={op(map(x->op(x),unks))}:
if setcont(eqs,unks)<>{op(unks)} then
   f2:=true
else
   f2:=false
fi:
if f2 then
   SADE[_decompvar]:={op(map(x->op(x),unks))}
fi:
v:={}:
for i from 1 to nops(unks) do
    v:=v union {op(unks[i])}
od:
v:=[op(v)]:
p:={}:
for i from 1 to nops(gs) do
    p:=p union charcrt(gs[i],unks,v)
od:
p minus {0}
end:
# Implementation - ODE SOLUTIONS
# ode_invsolution
#
# Computes invariant solutions of a single ODE given in eq, in the unknown function u,
# invariant with respect to the generator given by G.
#
ode_invsolution:=proc(eq,u,G)
local k,i,vars,eta,csi,ec,eq2,sol,res:
vars:=[op(0,u),op(u)]:
eta:=coeff(G,D[vars[1]]):
csi:=coeff(G,D[vars[2]]):
eta:=subs(vars[1]=u,eta):
csi:=subs(vars[1]=u,csi):
if csi=0 then RETURN({}) fi:
ec:=eta-diff(u,vars[2])*csi:
ec:={dsolve(ec,u)}:
res:={}:
for k from 1 to nops(ec) do
    eq2:=eval(subs(ec[k],eq)):
    sol:={solve(eq2,{_C1})}:
    for i from 1 to nops(sol) do
         res:=res union {subs(sol[i],ec[k])}
    od
od:
res
end:
# odesolver
#
# Reduces an ODE using a solvable Lie algebra or symmetry generators.
#
odesolver:=proc(eq,gen,u)
local i,j,p,p2,p3,v,u2,g,g2,alpha,beta,x,y,eq2,w,xo,yo,_w,tr,vs,ww,n,m,res,res2:
v:=[op(map(z->op(z),{op(u)}))]:
u2:=map(z->op(0,z),u):
if not(issolvable(gen,[op(u2),op(v)])) then
   ERROR(`Not a solvable Lie algebra`)
fi:
g:=canonical_basis(gen,eval([op(0,u[1]),op(v)])):
eq2:=eq:
xo:=v[1]:
yo:=u2[1]:
tr:=1:
vs:=[xo,yo]:
g2:=g[1]:
for i from 1 to nops(g)-1 do
    y:=cat(beta,i):
    x:=cat(alpha,i):
    w:=cat(ww,i):
    vs:=vs,[x,w]:
    p:=ode_reduce_order1(eq2,g2,yo,xo,w,x):
    eq2:=p[1]:
    if tr=1 then
       tr:=p[3]
    else
       tr:=tr,p[3]
    fi:
    g2:=genred(g[i+1],[tr],[vs]):
    xo:=x:
    yo:=w:
od:
w:=cat(ww,nops(g)):
x:=cat(alpha,nops(g)):
p:=ode_reduce_order1(eq2,g2,yo,xo,w,x):
if nops(g)=1 then
   tr:=[p[3]]
else
   tr:=[tr,p[3]]
fi:
vs:=[vs,[x,w]]:
eq2:=p[1]:
n:=nops(vs):
p:=vs[n][2](vs[n][1]):
p2:=p:
y:=vs[1][2]:
x:=vs[1][1]:
for i from 1 to n do
    tr:=subs(y(x)=_w2,subs(diff(y(x),x)=_w1,tr)):
    tr:=subs(y=y(x),tr):
    tr:=subs(_w2=y(x),_w1=diff(y(x),x),tr):
    if i<n then
       y:=vs[i+1][2]:
       x:=vs[i+1][1]
    fi
od:
m:=orddiff(whichder(eq,v,u2),v,u2)[1][2]:
if nops(g)=m and not(nargs>3 and has({args},transformation)) then
   res:={solve(eq2,{y(x)})} union {{0=0}}:
   res:=map(q->op(1,q[1])-op(2,q[1]),res) minus {0}:   for i from m to 1 by -1 do
       res2:={}:
       for j from 1 to nops(res) do
           p:=subs(vs[i+1][2](vs[i+1][1])=_w,res[j]):
           p:=subs(vs[i+1][1]=tr[i][1],p):
           p:=subs(_w=tr[i][2],p):
           p2:=traperror({dsolve(p,vs[i][2](vs[i][1]))}[1]):
           if p2=lasterror then
              p:=simplify(simplify(p,assume=positive),exp):
              p:=traperror({dsolve(p,vs[i][2](vs[i][1]))}[1])
           else
              p:=p2
           fi:
           p:=op(1,p)-op(2,p):
           res2:=res2 union {p}
       od:
       res:=res2
   od:
   p:=solve(res,{u[1]}):
   if {p}<>{} then res:=p fi:
else
   n:=nops(tr):
   p:=[vs[n+1][2](vs[n+1][1])=tr[n][2],vs[n+1][1]=tr[n][1]]:
   for i from n to 2 by -1 do
       p:=[vs[i][2](vs[i][1])=tr[i-1][2],vs[i][1]=tr[i-1][1]],p
   od:
   res:=[eq2,[p]]
fi:
res
end:
# ode_reduce_order1
#
# Reduces the order of eq in y0(x0) using the symmetry generator g.
# The resulting equation is in the new function y(x).
#
ode_reduce_order1:=proc(eq,g,y0,x0,y,x)
local eq2,ci,i,p,p1,p2,reg,_w,_u,dr,xi,clsol,r0:
clsol:=proc() local i,r:
r:=[args]:
if nops(r)=1 then RETURN(r[1]) fi:
for i from 1 to nops(r) do
    if not(has(r[i],I)) then RETURN(r[i]) fi
od
end:
ci:=casimir_invariant({g},[y0],[x0],[[1]]):
if has(ci[1],x0) then
   r0:=op(clsol(solve(ci[1]-x,{x0}))):
else
   r0:=op(clsol(solve(ci[1]-x,{y0})))
fi:
r0:=subs(y0=y0(x0),r0):
p1:=ci[1]:
p1:=subs(y0=y0(x0),p1):
xi:=subs(y0=y0(x0),ci[1]):
p2:=subs(_w=diff(y0(x0),x0),subs(y0=y0(x0),subs(diff(y0(x0),x0)=_w,ci[2]))):
dr:=whichder(eq,[x0],[y0]):
dr:=orddiff(dr,[x0],[y0]):
dr:=dr[1][2]:
reg:=y(x)=p2:
for i from 1 to dr-1 do
    p2:=simplify(diff(p2,x0)/diff(p1,x0)):
    reg:=reg,diff(y(x),x$i)=p2
od:
eq2:=eq:
if type(eq,`=`) then
   eq2:=op(1,eq)-op(2,eq2)
fi:
p:={}:
for i from dr to 1 by -1 do
    eq2:=subs(diff(y0(x0),x0$i)=cat(_w,i),eq2):
    reg:=op(subs(diff(y0(x0),x0$i)=cat(_w,i),[reg])):
    p:=p union {cat(_w,i)}
od:
eq2:=subs(y0(x0)=_w0,eq2):
reg:=op(subs(y0(x0)=_w0,[reg])):
reg:=solve({reg},p):
eq2:=subs(_w0=y0(x0),simplify(subs(r0,simplify(subs(reg,eq2))))):
eq2:=simplify(subs(r0,eq2),assume=positive):
eq2:=simpeqd(eq2,y):
[eq2,[y(x)=ci[2],r0],ci]
end:
# issolvable
#
# Tests for sovability of the Lie algebra with generators in a in the variables in v.
#
issolvable:=proc(a::set,v::list)
local p,nold:
p:=a:
nold:=10^100:
while p<>{} and nold>nops(p) do
      nold:=nops(p):
      p:=traperror(derived_subalg(p,v)):
      if p=lasterror then RETURN(false) fi
od:
if p={} then
   p:=true
else
   p:=false
fi:
p
end:
# casimir_invariant
#
# Computes the invariants up to orders k of the generators gens in the
# dependent variables u and independent variables x.
#
casimir_invariant:=proc(gens,u,x,kord)
local r,r2,i,j,j2,g,ders,p,p2,_w,a,k2,nn,inv,dv,phi,eqs,_gh,pr,k,n1,n2:
if has(kord,1) then
   k:=subs(1=2,kord)
else
   k:=kord
fi:
g:={}:
ders:={}:
p2:=_gh(op(u),op(x)):
for i from 1 to nops(gens) do
    p:=extend_gen(p2*gens[i],u,x,k):
    g:=g union {p[1]}
od:
p:=p[2]:
ders:=whichder3(g):
pr:={op(map(z->z(op(x)),u)),p2}:
ders:=map(z->if setcont(z,pr)={} then 0 else z fi,ders) minus {0}:
ders:=eval(subs(p2=1,ders)) minus {0}:
g:=eval(subs(p2=1,g)):
nn:=nops(p)+nops(u)+nops(x):
ders:=map(z->z[1],orddiff(ders,x,u)):
ders:=orddiff(ders,x,u):
ders:=map(z->z[1],ders):
dv:=op(x),op(u):
for i from 1 to nops(ders) do
    dv:=dv,cat(_w,i)
od:
for i from 1 to nops(p) do
    g:=subs(D[op(p[i])]=D[diff(u[p[i][1]](op(x)),op(map(z->x[z],p[i][2])))],g)
od:
for i from 1 to nops(ders) do
    g:=subs(ders[i]=cat(_w,i),g)
od:
a:=matrix(nops(gens),nn):
for i from 1 to nops(g) do
    for j from 1 to nops(x) do
        a[i,j]:=coeff(g[i],D[x[j]])
    od:
    for j from 1 to nops(u) do
        a[i,j+nops(x)]:=coeff(g[i],D[u[j]])
    od:
    for j from 1 to nops(p) do
        a[i,j+nops(x)+nops(u)]:=coeff(g[i],D[cat(_w,j)])
    od
od:
inv:=phi(dv):
dv:=[dv]:
r:=gaussolv(a,inv,dv):
if r={} then ERROR(`Unable to solve for the differential invariant`) fi:
r:=op(2,r[1]):
for i from 1 to nops(ders) do
    r:=subs(cat(_w,i)=ders[i],r):
od:
r2:={op(r)}:
r:=1:
for i from 1 to nops(r2)-1 do
    p:=estdiff(r2,x,u):
    j:=1:
    while j<=nops(r2) do
          if has(r2[j],p) or j=nops(r2) then
             r:=r,r2[j]:
             r2:=r2 minus {r2[j]}:
             j:=nops(r2)+1
          fi:
          j:=j+1
    od
od:
r:=[r]:
r:=simplify(expand([op(r2),op(2..nops(r),r)])):
# Now ordering the output by order.
r2:=map(z->whichder(z,x,u),r):
r2:=map(z->orddiff(z,x,u),r2):
p:=0:
for i from 1 to nops(r) do
    p2:=0:
    for j from 1 to nops(r2[i]) do
        if r2[i][j][2]>p2 then
           p2:=r2[i][j][2]
        fi
    od:
    p:=p,p2
od:
p:=[p]:
p:=p[2..nops(p)]:
r2:={seq([r[i],p[i]],i=1..nops(r))}:
n1:=min(p):
n2:=max(p):
r:=0:
for i from n1 to n2 do
    p2:=map(z->if z[2]=i then z[1] else 0 fi,r2) minus {0}:
    r:=r,op(p2)
od:
r:=[r]:
r:=r[2..nops(r)]:
r
end:
# reduce_ode_sist
#
# Reduces by one the dimension of a first order system of ODE's.
#
reduce_ode_sist:=proc(eqs,gen,u,x,v,y)
local i,_w,p,sr,un,ci,ci2,res,tr:
p:=eqs:
un:={}:
for i from 1 to nops(u) do
    p:=subs(diff(u[i](op(x)),x)=cat(_w,i),p):
    un:=un union {cat(_w,i)}
od:
sr:=traperror(solve(p,un)):
if sr=lasterror then
   ERROR(`Canot solve the system with respect to the derivatives.`)
fi:
ci:=casimir_invariant({gen},u,[x],[seq([0],i=1..nops(u))]):
ci2:=ci:
for i from 1 to nops(u) do
    ci2:=subs(u[i]=u[i](x),ci2)
od:
res:={}:
tr:={}:
for i from 2 to nops(ci) do
    p:=diff(ci2[i],x)/diff(ci2[1],x)-diff(v[i-1](y),y):
    tr:=tr union {diff(v[i-1](y),y)=diff(ci2[i],x)/diff(ci2[1],x)}:
    res:=res union {p}
od:
for i from 1 to nops(u) do
    res:=subs(diff(u[i](x),x)=cat(_w,i),res)
od:
res:=numer(simplify(subs(sr,res),assume=positive)):
[res,tr]
end:
# extend_gen
#
# Computes the extension of a given generator up to the k2-th order.
#
extend_gen:=proc(g,u,x,k2)
local n,m,eta,theta,eps,sr,i,j,l,l2,drv,drv2,u2,pr,pr2,vn,
      epsilon,res,nv,ordena,ordena2,vrs,k,p,p2,p3,grder,_a,fn:
#
ordena:=proc(a)
local r,i,j,b:
r:=a:
for i from 1 to nops(a)-1 do
    b:=r[i]:
    for j from i+1 to nops(a) do
        if r[j]<b then
           r[i]:=r[j]:
           r[j]:=b:
           b:=r[i]:
        fi
    od
od:
r
end:
#
ordena2:=proc(a)
local r,i,j,b:
r:=a:
for i from 1 to nops(a)-1 do
    b:=r[i]:
    for j from i+1 to nops(a) do
        if nops(r[j])<nops(b) then
           r[i]:=r[j]:
           r[j]:=b:
           b:=r[i]:
        fi
    od
od:
r
end:
#
grder:=proc(l,k)
local i,n:
n:=0:
for i from 1 to nops(l) do
    if l[i]=k then n:=n+1 fi
od:
n
end:
#
k:=max(op(map(z->op(z),k2))):
n:=nops(u):
m:=nops(x):
sr:=map(z->z=z(op(x)),u):
u2:=subs(sr,u):
drv:={seq([i],i=1..m)};
for i from 1 to k do
    drv2:={}:
    for j from 1 to m do
        drv2:=map(z->[op(z),j],drv) union drv2
    od:
    drv:=drv union drv2
od:
drv:=map(z->ordena(z),drv):
drv:=ordena2([op(drv)]):
drv2:=1:
for i from 1 to nops(drv) do
for j from 1 to nops(u) do
    p:=true:
    l:=1:
    while p and l<=nops(x) do
          if grder(drv[i],l)>k2[j][l] then
             p:=false
          fi:
          l:=l+1
    od:
    if p then
       drv2:=drv2,[j,drv[i]]
    fi
od
od:
drv2:=[drv2]:
drv:=[op(2..nops(drv2),drv2)]:
res:=g:
p3:=[op(map(y->coeff(g,D[y]),u)),op(map(y->coeff(g,D[y]),x))]:
p:=map(z->Diff(op(z[1],u),op(map(y->op(y,x),z[2]))),drv):
p2:=0:
for i from 1 to nops(p) do
    p2:=p2+cat(_a,i)*p[i]
od:
p:=infsym(p2,u,x,1):
p:=conv_diff(p):
res:=g:
for i from 1 to nops(drv) do
    res:=res+coeff(p,cat(_a,i))*D[op(drv[i])]
od:
vrs:=op(u),op(x):
for i from 1 to nops(u) do
    fn:=cat(eta,i):
    res:=eval(subs(fn(vrs)=p3[i],res))
od:
for i from 1 to nops(x) do
    fn:=cat(theta,i):
    res:=eval(subs(fn(vrs)=p3[i+nops(u)],res))
od:
[res,drv]
end:
# simpeqd
#
# Simplifie a differential equations removing unecessary terms not involving
# the unknown functions.
#
simpeqd:=proc(eq,y)
local r,r2,i:
r:=factor(eq):
if not(type(r,`*`)) then RETURN(r) fi:
r2:=1:
for i from 1 to nops(r) do
    if has(op(i,r),y) then
       r2:=r2*op(i,r)
    fi
od:
r2
end:
# genred
#
# Reduce a generator in a plane, relative to higher order differential invariants.
#
genred:=proc(g,tr,vs)
local i,reg,reg2,reg3,n,r0,s0,ri,si,rf,sf,_w,_nw,p1,p2,p,g2:
n:=nops(tr):
r0:=vs[1][1]:
s0:=vs[1][2]:
reg:=diff(s0(r0),r0$n)=cat(_w,n):
for i from n-1 to 1 by -1 do
    reg:=reg,diff(s0(r0),r0$i)=cat(_w,i)
od:
ri:=subs(s0=s0(r0),tr[1][1]):
si:=tr[1][2]:
for i from 2 to n do
    p1:=tr[i][1]:
    p2:=tr[i][2]:
    rf:=vs[i][1]:
    sf:=vs[i][2]:
    p1:=subs(rf=ri,subs(sf=si,p1)):
    p2:=subs(_nv=diff(sf(rf),rf),subs(sf=si,subs(diff(sf(rf),rf)=_nv,p2))):
    reg2:=rf=ri:
    reg3:=sf(rf)=si:
    p:=diff(sf(rf),rf)=diff(si,r0)/diff(subs(reg3,ri),r0):
    ri:=subs(reg3,p1):
    si:=subs(p,p2):
od:
ri:=subs(reg,ri):
si:=subs(reg,si):
p:=subs(reg,extend_gen(g,[s0],[r0],[[n+1]]))[1]:
p1:=seq(1,i=1..n-1):
p2:=seq(1,i=1..n):
reg2:=map(z->op(2,z)=op(1,z),{reg}):
g2:=subs(reg,p):
ri:=subs(s0(r0)=_w0,subs(reg,ri)):
si:=subs(s0(r0)=_w0,subs(reg,si)):
g2:=subs(s0=_w0,g2):
p1:=coeff(g2,D[r0])*diff(ri,r0)+coeff(g2,D[_w0])*diff(ri,_w0):
p2:=coeff(g2,D[r0])*diff(si,r0)+coeff(g2,D[_w0])*diff(si,_w0):
for i from 1 to n do
    p1:=p1+coeff(g2,D[1,[seq(1,j=1..i)]])*diff(ri,cat(_w,i)):
    p2:=p2+coeff(g2,D[1,[seq(1,j=1..i)]])*diff(si,cat(_w,i))
od:
rf:=vs[n+1][1]:
sf:=vs[n+1][2]:
g2:=p1*D[rf]+p2*D[sf]:
g2:=subs(reg,g2):
p:={ri-vs[n+1][1],si-vs[n+1][2]}:
p:=solve(p,{cat(_w,n-1),cat(_w,n)}):
g2:=subs(w0=s0(r0),subs(p,g2)):
g2
end:
# canonical_basis
#
# Returns the canonical basis from a set of generators a, in the variables in v.
#
canonical_basis:=proc(a::set,v::list)
local i,r,p,pold,nold,p2:
p:=a:
nold:=10^100:
r:=1:
while p<>{} and nold>nops(p) do
      nold:=nops(p):
      pold:=p:
      p:=derived_subalg(p,v):
      for i from 1 to nops(pold) do
          p2:=livec(p union {pold[i]},v):
          if nops(p2)=nops(p)+1 then
             r:=pold[i],r
          fi
      od
od:
r:=[r]:
r:=[op(1..nops(r)-1,r)]:
r
end:
# livec
#
# Returns the linearly inpendent differential operators (generators) of the
# set g in the variables v.
#
livec:=proc(g,v)
local u1,u2,u3,pold,_a,i,e,p,p2,res:
global SADE:
u1:=SADE[_system]:
u2:=SADE[_vars]:
u3:=SADE[_decompvar]:
pold:=SADE[traceout]:
SADE[traceout]:=false:
p:=0:
p2:={}:
for i from 1 to nops(g) do
    p:=p+_a(i)*g[i]:
    p2:=p2 union {_a(i)}
od:
e:=coeffs(expand(p),map(z->D[z],v)):
SADE[_decompvar]:={op(v)}:
SADE[_vars]:=SADE[_decompvar]:
SADE[_system]:=[{e},{},{}]:
decompfnc():
p:=SADE[_system][1]:
SADE[_system]:=u1:
SADE[_vars]:=u2:
SADE[_decompvar]:=u3:
SADE[traceout]:=pold:
p:=tautoelim(solve(p,p2)):
res:=g:
for i from 1 to nops(p) do
    if op(2,p[i])<>0 then
       res:=res minus {g[op(op(1,p[i]))]}
    fi
od:
res
end:
# derived_subalg
#
# Return the basis of generators of the derived sub-algebra of the
# algebra generated by the generators in gens, in the variables in v.
#
derived_subalg:=proc(a,v)
local res,i,j,k,p,p2,r,n,l,l2,_a,unks,b,u1,u2,u3,pold,g,vg,ro:
global SADE:
u1:=SADE[_system]:
u2:=SADE[_vars]:
u3:=SADE[_decompvar]:
pold:=SADE[traceout]:
SADE[traceout]:=false:
SADE[_decompvar]:={op(v)}:
SADE[_vars]:=SADE[_decompvar]:
n:=nops(a):
res:={}:
l:=0:
l2:=0:
unks:={}:
vg:={}:
b:=map(x->D[x],v):
for i from 1 to n do
    l:=l+cat(_a,i)*a[i]:
    l2:=l2+cat(_a,i)*g[i]:
    unks:=unks union {cat(_a,i)}:
    vg:=vg union {g[i]}
od:
SADE[parameters]:=unks:
for i from 1 to n-1 do
    for j from i+1 to n do
        p:=expand(comm(a[i],a[j],v)-l):
        p:={coeffs(p,b)}:
        SADE[_system]:=[p,{},{}]:
        decompfnc():
        p:=SADE[_system][1]:
        p:=tautoelim(solve(p,unks)):
        if setcont(p,v)<>{} or p={} then ERROR(`Not a closed set under commutation`) fi:
        k:=1:
        while k<=nops(unks) do
              if rhs(p[k])<>0 then
                 p:=map(z->lhs(z)=rhs(z)/rhs(p[k]),p):
                 k:=nops(unks)+1
              fi:
              k:=k+1
        od:
        r:=subs(p,l2):
        res:=res union {r}
    od
od:
res:=expand(res) minus {0}:
res:=eval(subs(g=a,res)) minus {0}:
res:=livec(res,v):
SADE[_system]:=u1:
SADE[_vars]:=u2:
SADE[_decompvar]:=u3:
SADE[traceout]:=pold:
res
end:
# gaussolv
#
# Solve for a linear partial differential system with coefficients in the matrix a,
# in the unkown function f, in variables v.
#
gaussolv:=proc(a,f,v)
local r,i,j,k,p,eqs,eqs2,n1,n2:
r:=linalg[gausselim](a):
r:=a:
eqs:={}:
n1:=linalg[rowdim](a):
n2:=linalg[coldim](a):
for i from 1 to n1 do
    p:=0:
    for j from 1 to n2 do
        if nops(v)>=j then
           p:=p+a[i,j]*diff(f,v[j])
        fi
    od:
    eqs:=eqs union {p}
od:
map(z->numer(z),eqs):
eqs2:=traperror(rifsimp(eqs,[f])):
if eqs2<>traperror and type(eqs2,array) then
   eqs:={op(eqs2[Solved])}
fi:
r:=pdsolve(eqs,{f}):
if type(r,list) then RETURN({}) fi:
r
end:
# dtot2
#
# Computes the total derivative of a with respect to b. The dependent and independet
# variables are given in the lists u and x, respectivelly.
#
dtot2:=proc(a,b,x,u)
local r,i:
r:=diff(a,b):
for i from 1 to nops(u) do
    r:=r+diff(a,u[i])*diff(u[i](op(x)),b)
od:
r
end:
# Implementation - Classification
# linear_rep
# #
# # Obtains the determining equations for the general liear equation defined by a differential operator.
# # The unknowns of the problem are stored in the global variable incognita. If the last argument is
# # determining then it return the determining equations for the unknowns.

#
linear_rep:=proc(Delta,simms,vvv,unk,nm)
local i,eqs,addeqs,_R,res,k,p:
global SADE:
#numger:=nops(simms):
if nargs=7 then
   addeqs:=args[7]
else
   addeqs:={}
fi:
SADE[var]:=vvv:
SADE[_vars]:=vvv:
SADE[incognita]:=unk:
SADE[fcount]:=1:
SADE[fname]:=fn:
eqs:={}:
for i from 1 to nops(simms) do
    eqs:=eqs union eqsimm(Delta,simms[i],_R||i):
    SADE[incognita]:=SADE[incognita] union {_R||i(op(SADE[var]))}
od:
SADE[_system]:=[eqs union addeqs,Delta,simms]:
if nargs=7 then
   SADE[parameters]:=args[7]
else
   SADE[parameters]:={}
fi:
if nargs>5 and has({args},determining) then
   RETURN(SADE[_system][1])
fi:
resolve():
res:=[SADE[_system][2],SADE[_system][1]]:
k:=1:
for i from 1 to nops(SADE[incognita]) do
    if has(res,SADE[incognita][i]) then
       p:=SADE[incognita][i]:
       if type(p,function) then
          p:=op(0,p)
       fi:
       res:=subs(p=cat(nm,k),res):
       k:=k+1
    fi
od:
res
end:
# eqsimm
#
# Auxiliary routine for eqsdet. Returns the set of equations for a given symmetry generator.
#
eqsimm:=proc(del,ger,rr)
local i,j,eqs,prov,prov2,rest,ds:
global SADE,_gh:
prov:=expand(comm(ger,del,SADE[var])-rr(op(SADE[var]))*del)+_gh:
ds:={}:
rest:=0:
for i from 1 to nops(prov) do
    prov2:=op(i,prov):
    if has(prov2,D) then
       if type(prov2,`*`) then
          for j from 1 to nops(prov2) do
              if has(op(j,prov2),D) then
                 ds:=ds union {op(j,prov2)}
              fi
          od
       else 
          ds:=ds union {prov2}
       fi
    else
       rest:=rest+prov2
    fi
od:
eqs:={subs(_gh=0,rest)}:#print(ds):
for i from 1 to nops(ds) do
    eqs:=eqs union {coeff(prov,ds[i])}:
    prov:=subs(ds[i]=0,prov)
od:
eqs:=subs(_gh=0,eqs union {prov}):
eqs
end:
# equivalence
#
# Returns all possible equations in the class defined by eq, with unknown functions unks, in the unknowns in v,
# admiting the symmetry generators in gens.
#
equivalence:=proc(eq,v::list,gens::set,unks::set)
local i,j,ds,eq2,eq3,rl,_eqnm,syst,lf,vrs,p,res,p2,p3,flag,flag2,wd,_gh,v2,dp,idp,rl2,wd2:
ds:=liesymmetries(eq,v,determining):
syst:={}:
lf:=ds[2]:
ds:=ds[1]:
vrs:=[op(lf[1])]:
for i from 1 to nops(gens) do
    p:=ds:
    for j from 1 to nops(vrs) do
        p:=eval(subs(lf[j]=coeff(gens[i],D[vrs[j]]),p))
    od:
    syst:=syst union p
od:
syst:=syst minus {0}:
if syst={} then
   RETURN([eq,{}])
fi:
flag:=true:
p:=nldsolve(syst,unks):
res:={}:
for i from 1 to nops(p) do
    res:=res union {[eval(subs(p[i][1],eq)),p[i][2]]}
od:
res
end:
# equiv_aux
#
# Looks for derivatives in eq of functions not in v in eq and replaces them by functions names.
# The arranged system is given in the first element of the list in the output
# and the retun rule is given as its second element unsing variable names specified by nm.1 nm.2 etc...
#
equiv_aux:=proc(eq,v::list,nm)
local i,res,res2,p,dv,dep,indep,fr:
fr:=proc(x) local y: y:=x: while has(y,diff) do y:=op(1,y) od: op(0,y) end:
p:=whichder(eq):
dv:={}:
for i from 1 to nops(p) do
    if setcont(p[i],v)={} then
       dv:=dv union {p[i]}
    fi
od:
res:=eq:
res2:=0:
dep:=[op(map(x->fr(x),dv))]:
indep:=map(x->op(x),v):
dv:=map(x->x[1],orddiff(dv,indep,dep)):
for i from 1 to nops(dv) do
    p:=op(setcont(dv[i],indep)):
    res:=subs(dv[i]=cat(nm,i)(p),res):
    res2:=res2,cat(nm,i)(p)=dv[i]
od:
res2:=[res2]:
res2:=res2[2..nops(res2)]:
[res,res2]
end:
# Implementation - Standard form
# isdiffgt
#
# Tests for two derivatives a and b if a>b for the total degree-lexicographic
# ordering specified by the independet variables in the list v and the
# dependent variables in the list u.
#
isdiffgt:=proc(a,b,v,u)
local i,d1,d2,n1,n2:
options remember:
d1:=tonuple(whichderlist(a,v),v):
d2:=tonuple(whichderlist(b,v),v):
n1:=0:
n2:=0:
for i from 1 to nops(v) do
    n1:=n1+d1[i]:
    n2:=n2+d2[i]
od:
if n1>n2 then RETURN(true) fi:
if n1<n2 then RETURN(false) fi:
n1:=posvars(op(setcont(a,u)),u):
n2:=posvars(op(setcont(b,u)),u):
if n1<n2 then RETURN(true) fi:
if n1>n2 then RETURN(false) fi:
if gtlex(d1,d2) then RETURN(true) fi:
false
end:
# isdiffgt_purelex
#
# Tests if derivative a>b using the pure lexicographic ordering,
# with independent variables in v and dependent variables in u.
#
isdiffgt_purelex:=proc(a,b,v,u)
local i,ua,ub,na,nb,dva,dvb,ka,kb,nv,pva,pvb:
ua:=op(setcont(a,u)):
ub:=op(setcont(b,u)):
na:=posvars(ua,u):
nb:=posvars(ub,u):
if na>nb then RETURN(true) fi:
if na<nb then RETURN(false) fi:
dva:=whichderlist(a,v):
dvb:=whichderlist(b,v):
nv:=nops(v):
ka:=array(1..nv,[seq(0,i=1..nv)]):
kb:=array(1..nv,[seq(0,i=1..nv)]):
for i from 1 to nops(dva) do
    pva:=posvars(dva[i],v):
    ka[pva]:=ka[pva]+1
od:
for i from 1 to nops(dvb) do
    pvb:=posvars(dvb[i],v):
    kb[pvb]:=kb[pvb]+1
od:
for i from nv to 1 by -1 do
    if ka[i]>kb[i] then
       RETURN(true)
    fi:
    if ka[i]<kb[i] then
       RETURN(false)
    fi
od:
false
end:
# highestdiff
#
# Returns the highest derivative in the expression a, using the ordering specified in SADE[_difforder]
# ordering as specified by the lists v (independent variables) and u (dependent variables).
#
highestdiff:=proc(a,v,u)
local i,p,r,b,fl:
options remember:
b:=a:
if type(b,`=`) then
   b:=op(2,b)-op(1,b)
fi:
b:=numer(b):
p:=whichder2(b,u):
r:=p[1]:
for i from 2 to nops(p) do
    if SADE[_difforder]=_tdeglex then
       fl:=isdiffgt(p[i],r,v,u)
    else
       if SADE[_difforder]=_purelex then
          fl:=isdiffgt_purelex(p[i],r,v,u):
       else
          ERROR("Unknown differential order")
       fi
    fi:
    if fl then
       r:=p[i]:
    fi
od:
r
end:
# lowestdiff_var
#
# Returns the variable in v with the lowest derivative of function f in expression a,
# and the corresponding derivative order.
#
lowestdiff_var:=proc(a,f,v)
local i,r,drvs,drvord,pr:
drvs:=setcontonly(whichder(a),f):
drvord:=10^1000:
for i from 1 to nops(v) do
    pr:=highestdiff(drvs,[v[i]],[op(0,f)]):
    pr:=orddiff({pr},[v[i]],[op(0,f)]):
    if pr[1][4][1]<drvord then
       drvord:=pr[1][4][1]:
       r:=v[i]
    fi
od:
[r,drvord,f]
end:
# subsexp
#
# Used to replace derivatives to avoid implicit substitutions. Only
# the exact derivative is replaced.
#
subsexp:=proc(a,b)
local a2,b2,r:
a2:=convert(a,D):
b2:=convert(b,D):
r:=subs(a2,b2):
r:=convert(r,diff):
r
end:
# solvhigh
#
# Solve the equation eq for its highest derivative as given by the
# orderings v and u of the independent and dependent variables, respectivelly.
#
solvhigh:=proc(eq,v,u)
local hd,r:
#
#
if not(has(eq,diff)) then ERROR(` oops `) fi:
#
#
hd:=highestdiff(eq,v,u):
r:=[solve(eq,{hd})]:
r:=op(r[1]):
r
end:
# subsdom
#
# Replaces for each dominant derivative of each equation in the set (or list) ee
# in the remaining equations, starting from the highest derivative of all equations.
# then going in descending order. The ordering is specified by the independent variables
# list v and the dependent variables list u. If the fourth argument is `dominant` it replaces
# only explicit appearances of the dominant derivative. If it is `nontrivial` it replaces
# also for its non-trivial derivatives.
#
subsdom:=proc(ee,v,u,t)
local i,j,f,n,eqs,hds,hdold,rhsold,fl,p1,p2,p,e:
e:=sizeorder2(ee):
n:=nops(e):
eqs:=array(1..n):
hds:=array(1..n):
for i from 1 to n do
    eqs[i]:=e[i]:
    if not(type(eqs[i],`=`)) or (type(eqs[i],`=`) and op(1,eqs[i])=0) then
       p1:=traperror(solvhigh(eqs[i],v,u)):
       if p1=lasterror then
          eqs[i]:=simplify(eqs[i]):
          if not(type(eqs[i],`=`)) then
             eqs[i]:=0=eqs[i]
          fi:
       else
          eqs[i]:=p1
       fi
    fi:
    hds[i]:=op(1,eqs[i])
od:
f:=true:
fl:=array(1..n):
while f do
      f:=false:
      for i from 1 to n do
          for j from 1 to n do
              fl[j]:=false:
              if i<>j and op(1,eqs[j])<>op(2,eqs[j]) and op(1,eqs[i])<>op(2,eqs[i]) then
                 hdold:=op(1,eqs[j]):
                 rhsold:=op(2,eqs[j]):
                 if setcont(eqs[j],setcont(hdold,u))<>{} then
                    if t=`dominant` then
                       p1:=convert(eqs[i],D):
                       p2:=convert(eqs[j],D):
                       eqs[j]:=conv_diff(subs(p1,p2))
                    fi:
                    if t=`nontrivial` then
                       eqs[j]:=subeq(eqs[i],eqs[j],v,u)
                    fi
                 fi:
                 if hdold<>op(1,eqs[j]) then
                    fl[j]:=true:
                    f:=true:
                    eqs[j]:=expand(eqs[j])
                 else
                    if op(2,eqs[j])<>rhsold then
                       f:=true:
                       eqs[j]:=expand(eqs[j])
                    fi
                 fi
              fi
          od:
          for j from 1 to n do
              if i<>j and fl[j] then
                 eqs[j]:=numer(op(2,eqs[j])-op(1,eqs[j])):
                 if eqs[j]<>0 then
                    p:=traperror(solvhigh(eqs[j],v,u)):
                    if p=lasterror then
                       eqs[j]:=0=simplify(eqs[j])
                    else
                       eqs[j]:=p
                    fi
                 else
                    eqs[j]:=0=0
                 fi
              fi
          od
      od
od:
eqs:=convert(eqs,set) minus {0=0}:
eqs
end:
# subsdom_simp
#
# Replaces for each dominant derivative of each equation in the set (or list) ee
# in the remaining equations, starting from the highest derivative of all equations.
# then going in descending order. The ordering is specified by the independent variables
# list v and the dependent variables list u.
# This version only replaces those derivatives recognized by the maple subs.
#
subsdom_simp:=proc(ee,v,u)
local i,j,f,n,eqs,hds,hdold,rhsold,fl,p,p1,e,ccnt:
e:=sizeorder2(ee):
n:=nops(e):
eqs:=array(1..n):
hds:=array(1..n):
for i from 1 to n do
    eqs[i]:=e[i]:
    if not(type(eqs[i],`=`)) or (type(eqs[i],`=`) and op(1,eqs[i])=0) then
       p1:=traperror(solvhigh(eqs[i],v,u)):
       if p1=lasterror then
          eqs[i]:=simplify(eqs[i]):
          if not(type(eqs[i],`=`)) then
             eqs[i]:=0=eqs[i]
          fi:
       else
          eqs[i]:=p1
       fi
    fi:
    hds[i]:=op(1,eqs[i])
od:
f:=true:
fl:=array(1..n):
ccnt:=0:
while f and ccnt<100 do
      f:=false:
      for i from 1 to n do
          for j from 1 to n do
              fl[j]:=false:
              if i<>j and op(1,eqs[j])<>op(2,eqs[j]) and op(1,eqs[i])<>op(2,eqs[i]) then
                 hdold:=conv_diff(op(1,eqs[j])):
#                 hdold:=op(1,eqs[j]):
                 rhsold:=conv_diff(op(2,eqs[j])):
#                 rhsold:=op(2,eqs[j]):
#                 eqs[j]:=simplify(eval(subs(conv_diff(eqs[i]),conv_diff(eqs[j])))):
                 eqs[j]:=expand(eval(subs(conv_diff(eqs[i]),conv_diff(eqs[j])))):
#                 eqs[j]:=expand(eval(subs(eqs[i],eqs[j]))):
                 eqs[j]:=conv_diff(eqs[j]):
ccnt:=ccnt+1:
                 if hdold<>op(1,eqs[j]) then
                    fl[j]:=true:
                    f:=true:
                    eqs[j]:=expand(eqs[j])
                 else
                    if expand(op(2,eqs[j]))<>expand(rhsold) then
                       f:=true:
                       eqs[j]:=expand(eqs[j])
                    fi
                 fi
              fi
          od:
          for j from 1 to n do
              if i<>j and fl[j] then
#####                 eqs[j]:=numer(op(2,eqs[j])-op(1,eqs[j])):
                 eqs[j]:=op(2,eqs[j])-op(1,eqs[j]):
                 if eqs[j]<>0 then
                    p:=traperror(solvhigh(eqs[j],v,u)):
                    if p=lasterror then
                       eqs[j]:=0=simplify(eqs[j])
                    else
                       eqs[j]:=p
                    fi
                 else
                    eqs[j]:=0=0
                 fi
              fi
          od
      od
od:
eqs:=convert(eqs,set) minus {0=0}:
eqs
end:
# conv_diff
#
# Converts to a form using diff instead of D.
#
conv_diff:=proc(ain)
local dr,i,r,p,p2,a:
a:=convert(ain,diff):
if not(has(a,D)) then
   RETURN(a)
fi:
dr:=whichder(a):
r:=a:
for i from 1 to nops(dr) do
    p:=dr[i]:
    p2:=convert(p,D):
    r:=subs(p2=p,r)
od:
r
end:
# orthoform
#
# Computes the orthonomic form of the system e, with independent variables v
# and dependent variables u. The order in the lists v and u is used for
# derivatives ordering.
#
orthoform:=proc(e,v,u)
local i,p,f,r,r2,old,cc:
global SADE:
SADE[_difforder]:=_tdeglex:
f:=true:
if type(e,set) or type(e,list) then
   r:=e
else
   r:={e}
fi:
if type(r[1],`=`) then
   r:=map(x->op(1,x)-op(2,x),r)
fi:
cc:=0:
while f and cc<100 do ########################### <<<<<<<<<<<<<< HERE
cc:=cc+1:
      old:=r:
      r:=subsdom_simp(r,v,u):
      r:=subsdom(r,v,u,`dominant`):
      r:=subsdom(r,v,u,`nontrivial`):
      f:=evalb(r<>old)
od:
##############
r:=map(x->if op(1,x)=op(2,x) then 0 else x fi,r) minus {0}:
##############
r
end:
# orddiff
#
# Returns the list of derivatives in descending order with respect to
# the corresponding ordering in the form a list of lists.
# Each element is a list with four elements: the first element is the
# the corresponding derivative, the second element is
# its order, the third element the position of the derivative in the
# input list d and the fourth element is the list with the coordinates
# of the derivative. The ordering is specified by the lists v and u, of the
# independent and dependent variables, respectivelly.
#
orddiff:=proc(d,v,u)
local i,j,r,s,p,p2,p3:
r:=array(1..nops(d)):
s:=convert(d,set):
for i from 1 to nops(d) do
    p:=highestdiff(s,v,u):
    p2:=tonuple(whichderlist(p,v,u),v,u):
    p3:=0:
    for j from 1 to nops(v) do p3:=p3+p2[j] od:
    r[i]:=[p,p3,posvars(p,d),p2]:
    s:=s minus {p}:
od:
r:=convert(r,list):
r
end:
# subeq
#
# Replaces the substitution rule e1 in e2 considering implicit substitutions.
# The lists v and u are the independent and dependent variables in
# the specified order.
#
subeq:=proc(e1,e2,v,u)
local i,p,p2,eq2,t1,t2,l,r:
if type(e2,set) or type(e2,list) then
   p:={}:
   for i from 1 to nops(e2) do
       p:=p union {subeq(e1,e2[i],v,u)}
   od:
   RETURN(p)
fi:
eq2:=e2:
if type(eq2,`=`) then
   eq2:=op(2,eq2)-op(1,eq2)
fi:
p:=whichder2(eq2,u):
p2:={}:
t1:=op(1,e1):
t2:=op(2,e1):
for i from 1 to nops(p) do
    if setcont(t1,u)=setcont(p[i],u) then
       p2:=p2 union {p[i]}
    fi
od:
r:={}:
l:=tonuple(whichderlist2(t1,v),v):
for i from 1 to nops(p2) do
    p:=tonuple(whichderlist2(p2[i],v),v):
    p:=listminus(p,l):
    if p<>false then
       p:=listdiff(t1,p,v)=listdiff(t2,p,v):
       r:=r union {p}
    fi
od:
eq2:=subs(r,e2):
if type(eq2,`=`) and op(1,eq2)<>op(1,e2) then
   eq2:=0=numer(op(2,eq2)-op(1,eq2))
fi:
eq2
end:
# listdiff
#
# Returns the expression a derived with respect to the variables represented
# in the coordinates list b, relative to the order in variable list v.
#
listdiff:=proc(a,b,v)
local i,r:
option remember:
r:=a:
for i from 1 to nops(b) do
    if b[i]>0 then
       r:=diff(r,v[i]$b[i])
    fi
od:
r
end:
# listminus
#
# Subtracts the elements of the list b from the corresponding elements of list a.
# If any element of the result is negative, it returns false.
# 
listminus:=proc(a,b)
local i,r:
options remember:
r:=1:
for i from 1 to nops(a) do
    if a[i]<b[i] then
       RETURN(false)
    fi:
    r:=r,a[i]-b[i]
od:
r:=[r]:
r:=[op(2..nops(r),r)]:
r
end:
# tonuple
#
# Converts a list of derivation variables to a n-uple of coordinates
# relative to the variable list v.
#
tonuple:=proc(l,v)
local r,i,n:
options remember:
r:=array(1..nops(v)):
for i from 1 to nops(v) do
    r[i]:=0
od:
for i from 1 to nops(l) do
    n:=posvars(l[i],v):
    if n>0 then
       r[n]:=r[n]+1
    fi
od:
r:=convert(r,list):
r
end:
# whichderlist2
#
# Returns a list with all derivation variables in the set or list v, with repetitions.
#
whichderlist2:=proc(a,v)
local res,a2:
options remember:
res:=1:
a2:=a:
while has(a2,diff) or has(a2,Diff) do
      res:=res,op(2..nops(a2),a2):
      a2:=op(1,a2)
od:
res:=[res]:
res:=[op(2..nops(res),res)]:
res
end:
# gtlex
#
# Tests for n-uples if a>b in the lexicographic order.
#
gtlex:=proc(a,b)
local i:
options remember:
if nops(a)<>nops(b) then
   ERROR(`number of elements of n-uples different.`)
fi:
for i from 1 to nops(a) do
    if a[i]>b[i] then
       RETURN(true)
    else if a[i]<b[i] then
            RETURN(false)
         fi
    fi
od:
false
end:
# sizeorder2
#
# Returns a list of equations reordered in ascending order of number of terms.
#
sizeorder2:=proc(eqs)
local i,j,pos,eqs2,res,n,prov,prov2,m,m2:
eqs2:={op(expand(eqs))} minus {0=0}:
n:=nops(eqs2):
res:=array(1..n):
for i from 1 to n do
    prov:=op(1,eqs2[1])-op(2,eqs2[1]):
    if type(prov,`+`) then
       m:=nops(prov)
    else
       m:=1
    fi:
    pos:=1:
    for j from 2 to nops(eqs2) do
        prov2:=op(1,eqs2[j])-op(2,eqs2[j]):
        if type(prov2,`+`) then
           m2:=nops(prov2)
        else
           m2:=1
        fi:
        if m2<m then
           m:=m2:
           pos:=j
        fi
    od:
    res[i]:=eqs2[pos]:
    eqs2:=eqs2 minus {eqs2[pos]}
od:
eqs2:=0:
for i from 1 to n do
    eqs2:=eqs2,res[i]
od:
eqs2:=[op(2..n+1,[eqs2])]:
eqs2
end:
# countvarlist
#
# Count how many times the variable v occurs in the list l of variable names.
#
countvarlist:=proc(a,l)
local n,i:
n:=0:
for i from 1 to nops(l) do
    if l[i]=a then
       n:=n+1
    fi
od:
n
end:
# diffcoeff
#
# Returns the coefficient of the derivative in dr in equation in eq, in functions in funcs.
#
diffcoeff:=proc(eq,dr,indep,dep)
local i,res,wd,_ddr,vc,eq2,bck,_g:
wd:=whichder(eq):
wd:=map(x->if setcont(x,dep)={} then 1 else x fi,wd) minus {1}:
wd:=map(x->x[1],orddiff(wd,indep,dep)):
eq2:=eq:
if not(has(dr,diff)) then
   for i from 1 to nops(wd) do
       eq2:=subs(wd[i]=0,eq2)
   od:
   #eq2:=subs(dr=_g,eq2):
   RETURN(coeff(eq2,dr))
fi:
bck:={}:
for i from 1 to nops(wd) do
    eq2:=subs(wd[i]=cat(_ddr,i),eq2):
    bck:=bck union {cat(_ddr,i)=wd[i]}:
    if wd[i]=dr then
       vc:=cat(_ddr,i)
    fi
od:
res:=subs(bck,coeff(eq2,vc)):
res
end:
# clean_eqs
#
# Removes any unecessary factor from each equation.
#
clean_eqs:=proc(eqs,unks)
local i,j,res,pr,pr2,ee,nn:
ee:=convert([op(eqs)],array):
nn:=nops(eqs):
res:=array(1..nn):
for i from 1 to nn do
    pr:=factor(ee[i]):
    if type(pr,`*`) then
       pr2:=1:
       for j from 1 to nops(pr) do
           if setcont(op(j,pr),unks)<>{} then
              pr2:=pr2*op(j,pr)
           fi
       od:
       pr:=pr2
    fi:
    res[i]:=pr
od:
res:=convert(res,set):
res
end:
# dspoly
#
# Computes the cross-differentiation of polynomial pa and pb, with respect
# to the specified ordering and  independent variables in v and dependent
# variables in u
#
dspoly:=proc(pa,pb,v,u)
local i,res,drva,drvb,vra,vrb,newpa,newpb,na,nb,hda,hdb,neweq,flag,z:
drva:=highestdiff(pa,v,u):
drvb:=highestdiff(pb,v,u):
if setcont(drva,u)<>setcont(drvb,u) then
   RETURN(0)
fi:
vra:=whichderlist(drva,{op(v)}):
vrb:=whichderlist(drvb,{op(v)}):
newpa:=pa:
newpb:=pb:
for i from 1 to nops(v) do
    na:=countvarlist(v[i],vra):
    nb:=countvarlist(v[i],vrb):
    if na<>nb then
       #flag:=true:
       if na>nb then
          newpb:=diff(newpb,v[i]$(na-nb))
       else
          newpa:=diff(newpa,v[i]$(nb-na))
       fi
    fi
od:
hda:=highestdiff(newpa,v,u):
hda:=diffcoeff(newpa,hda,v,u):
hdb:=highestdiff(newpb,v,u):
hdb:=diffcoeff(newpb,hdb,v,u):
neweq:=hda*newpb-hdb*newpa:
z:=traperror(gcd(hda,hdb)):
if z<>lasterror then
   res:=expand(neweq/z)
else
   res:=neweq
fi:
res:=op(clean_eqs({res},u)):
res:
end:
# pseudored
#
# Pseudo reduce pa with respect to pb, with independent and
# dependent variables in v an u respectivelly.
#
pseudored:=proc(pa,pb,v,u)
local i,res,wda,hdb,drb,pr,hcoef,fa,fb,_gh,z,hcfb:
wda:=whichder(pa):
wda:=orddiff(wda,v,u):
hdb:=highestdiff(pb,v,u):
hdb:=orddiff({hdb},v,u):
fa:=pa:
for i from 1 to nops(wda) do
    fa:=subs(wda[i][1]=_gh,fa):
    if setcont(wda[i][1],u)=setcont(hdb[1][1],u) then
       pr:=listminus(wda[i][4],hdb[1][4]):
       if pr<>false then
          fb:=listdiff(pb,pr,v):
          fa:=coeff(fa,_gh,1):
          hcfb:=highestdiff(fb,v,u):
          hcfb:=subs(hcfb=_gh,fb):
          hcfb:=coeff(hcfb,_gh,1):
          z:=gcd(hcfb,fa):
          res:=simplify((hcfb*pa-fa*fb)/z):
          RETURN(res)
       fi:
    fi:
    fa:=subs(_gh=0,fa):
od:
pa
end:
# pseudonormal
#
# Computes the peudo normal form of f with respect to the set (or list)
# of equations in g, with independent varibles in v and dependent variables in u.
#
pseudonormal:=proc(f,g,v,u)
local i,res,old:
res:=f:
while old<>res do
      old:=res:
      for i from 1 to nops(g) do
          res:=expand(pseudored(res,g[i],v,u)):
      od
od:
res
end:
# highcoeff
#
# Returns the coefficient of the highest derivative in f, with indep variables in v and dep variables in u.
#
highcoeff:=proc(f,v,u)
local res,pr,_gh:
pr:=highestdiff(f,v,u):
res:=subs(pr=_gh,f):
res:=coeff(res,_gh):
res
end:
# KolchinRittSort
#
# Implementation of the Kolchin-Rit algorithm with sorting.
#
KolchinRittSort:=proc(eqs,v,u,ordering)
local i,j,sig,sig2,orderold,pairsdone,f1,f2,pair,h,sigdone,sigrest,_gh,flag,old:
global SADE:
if ordering<>_tdeglex and ordering<>_purelex then
   ERROR("Wrong type of ordering")
fi:
orderold:=SADE[_difforder]:
SADE[_difforder]:=ordering:
flag:=true:
sig:=eqs:
while flag do
      sig:=sizeorder(clean_eqs(sig,u)):
      sigdone:={}:
      sigrest:={}:
      i:=1:
      for i from 1 to nops(sig) do
          if nops(expand(sig[i])+_gh)-1=1 then
             sigdone:=sigdone union {sig[i]}
          else
             sigrest:=sigrest union {sig[i]=0}
          fi
      od:
      if sigdone={} then
         flag:=false
      else
         sigdone:=orthoform(sigdone,v,u):
         if sigrest={} then
            old:={}
         else
            old:=whichder2(sigrest,u)
         fi:
         if sigrest={} then
            flag:=false
         else
            for i from 1 to nops(sigdone) do
                sigrest:=map(x->subeq(sigdone[i],x,v,u),sigrest)
            od:
            sigrest:=map(x->op(1,x)-op(2,x),sigrest) minus {0}:
            if not(sigrest={}) and whichder2(sigrest,u)=old then
               flag:=false
            fi
         fi:
         sigdone:=map(x->op(1,x)-op(2,x),sigdone):
         sig:=sigrest union sigdone minus {0}
      fi
od:
sig:={op(sig)} minus {0}:
sig:=sizeorder(clean_eqs(sig,u)):
i:=1:
j:=2:
pairsdone:={}:
sig2:=sig:
while i<=nops(sig2) and nops(sig2)>1 do
      f1:=sig2[i]:
      f2:=sig2[j]:
      pair:={f1,f2}:
      if not(pair in pairsdone) then
         pairsdone:=pairsdone union {pair}:
         h:=op(clean_eqs({dspoly(f2,f1,v,u)},u)):
         if has(h,sig2) or h=0 then
            h:=0
         else
            h:=pseudonormal(h,sig2,v,u):
            h:=op(clean_eqs({h},u)):
         fi:
         if h<>0 then
            if type(h,function) then
               #sig2:={op(eval(subeq(h=0,sig2,v,u)))} minus {0}:
               sig2:=clean_eqs({op(map(x->subeq(h=0,x,v,u),sig2))} minus {0},u)
            fi:
            sig2:=[op(sig2),h]:
            sig2:=sizeorder(sig2):
           i:=1:
            j:=2
         fi
      else
         if j=nops(sig2) then
            j:=i+2:
            if j>nops(sig2) then
               i:=nops(sig2)+1
            else
               i:=i+1
            fi
         else
            j:=j+1
         fi
      fi
od:
SADE[_difforder]:=orderold:
sig2
end:
# KolchinRitt
#
# Progressive Kolchin-Ritt algorithm
#
KolchinRitt:=proc(eqs,v,u,ordering)
local res,ne,sorteq,m,mini,mfin,pr:
global SADE:
if not(type(SADE[_KCincrement],constant)) then
   SADE[_KCincrement]:=5
fi:
ne:=SADE[_KCincrement]:
sorteq:=sizeorder(eqs):
m:=nops(sorteq):
mini:=1:
mfin:=min(m,ne):
res:=KolchinRittSort(sorteq[mini..mfin],v,u,ordering):
while mfin<m do
      mini:=mfin+1:
      mfin:=min(m,mfin+ne-1):
      if mini=m then
         res:={op(res),sorteq[m]}
      else
         pr:={op(sorteq[mini..mfin])} union {op(res)} minus {0}:
         res:=KolchinRittSort(pr,v,u,ordering)
      fi
od:
res
end:
# Implementation - QPSI
# conserved
#
# Computes the Quasi-Polinomial constants of motion of a first-orde Quasi-Polynomial
# system of ODE`s. The input is given by the equations set, variable names,
# the set of free parameters, the order of the quasi-invariants used in the computation,
# and the options. Possible options are: positive which indicates that the final
# expressions are simplified in the positive orthant, and Groebner, which
# tells the routine to use a Groebner basis computation for the solution of the
# determining system of the quasi-invariants.
# If an optional argument is given as surfaces, then the routine return a set
# of invariant surfaces of the system as a set of lists. The first element defines the surface
# (=0) and the second elements gives the conditions on the free parameters for the surface
# be invariant.
#
conserved:=proc()
local i,j,n,eq,equations,variables,time,parameters,flag,flag2,res,res2,prov,prov2,tts:
equations:=args[1]:
variables:=args[2]:
if type(variables[1],function) then
   parameters:=args[3]:
   n:=args[4]
else
   time:=args[3]:
   parameters:=args[4]:
   n:=args[5]
fi:
if has({args},Groebner) then flag:=true else flag:=false fi:
if has({args},positive) then flag2:=true else flag2:=false fi:
if type(variables[1],function) then
   LVformat(equations,variables,parameters)
else
   LVformat(equations,variables,time,parameters)
fi:
eq:=quasisyst(n):
if flag then
   res:=quasisolve(eq,Groebner)
else
   res:=quasisolve(eq)
fi:
if has({args},surfaces) then
   res:=final_form(res):
   res:=map(x->[subs(x[3],x[1]),x[3]],res):
   RETURN(res)
fi:
res:=invariant(res,t):
tts:={}:
i:=1:
while has(res,cat(_tt,i)) do
      tts:=tts union{cat(_tt,i)}:
      i:=i+1
od:
res2:={}:
for i from 1 to nops(res) do
    if flag2 then
       prov:=traperror(simplify(res[i],assume=positive))
    else
       prov:=traperror(simplify(res[i]))
    fi:
    if prov<>lasterror then
       res2:=res2 union {prov}
    fi
od:
if type(variables[1],function) then
   variables:=map(x->op(0,x),variables)
fi:
res:={}:
for i from 1 to nops(res2) do
    prov2:=res2[i][1]:
    if setcont(prov2,variables)<>{} then
       prov:=setcont(res2[i][1],tts):
       if prov<>{} then
          for j from 1 to nops(prov) do
              prov2:=subs(prov[j]=cat(_C,j),prov2)
          od
       fi:
       res:=res union {[prov2,res2[i][2]]}
    fi
od:
res
end:
# LVformat
# Reduces a system of first order Quasi-Polynomial differential equations to the Lotka-Volterra format.
# Synopsis
# result := LVformat(equations,variables,time,parameters)
# Parameters
# result : a list with the first element as the vector field (a list) of the associated Lotka-Volterra
#               system and the second element the list of the corresponding Quasi-Monomial variables.
# equations: a set of differential equations.
# variables: a set of variable names.
# time: a variable name (the time variable).
# parameters: a set with the free parameters in the system.
# Description
# Reduces a system of first order Quasi-Polynomial differential equations to the Lotka-Volterra format.
# In case the resulting system os not of the Quasi-Polynomial format an error message is issued.
# Code
LVformat:=proc()
local i,sol,flw,vr,equations,vars,time,parameters:
equations:=args[1]:
vars:=args[2]:
if type(vars[1],function) then
   equations:=convert(equations,Diff):
   time:=op(1,vars[1]):
   for i from 1 to nops(vars) do
       equations:=subs(vars[i]=op(0,vars[i]),equations)
   od:
   vars:=map(x->op(0,x),vars):
   parameters:=args[3]
else
   time:=args[3]:
   parameters:=args[4]
fi:
sol:=eqToCauchy(equations,vars,time):
flw:=sol[1]:
vr:=sol[2]:
algsys(flw,vr,parameters)
end:
# eqToCauchy
# Transformts a system of first order differential equations to the Caychy form.
# Synopsis
# result := eqToCauchy(equations,variables,time)
# Parameters
# result : a list with the first element as the components of the vector field of the associated system
#               in the Cauchy form and the secon element with the corresponding variable names.
# equations: a set of differential equations.
# variables: a set of variable names.
# time: a variable name (the time variable).
# Description
# Transforms a system of first order differential equations in the Caychy form and returns the components of
# the associated vector field (the flow), and the resctive variables.
# Code
eqToCauchy:=proc(equations,vars,time)
local unks,sol,flw,vr,i:
unks:={}:
for i from 1 to nops(vars) do
    unks:=unks union {Diff(vars[i],time)}
od:
sol:=solve(equations,unks):
flw:=op(2,sol[1]):
if not(isQP(op(2,sol[1]),vars)) then
   error `The resulting equation is not of the QP format`
fi:
vr:=op(1,op(1,sol[1])):
for i from 2 to nops(sol) do
    if not(isQP(op(2,sol[i]),vars)) then
       error `The resulting equation is not of the QP format`
    fi:
    flw:=flw,op(2,sol[i]):
    vr:=vr,op(1,op(1,sol[i]))
od:
flw:=[flw]:
vr:=[vr]:
[flw,vr]
end:
# isQM
# Tests if an expression is a Quasi-Monomial.
# Synopsis
# result := isQM(expression,variables)
# Parameters
# result : a boolean valule (true or false).
# expression: a maple expression.
# variables: a set of variable names.
# Description
# Tests if a given expression is a Quasi-Monomial in the specified variables.
# Code
isQM:=proc(a,vars)
local res,i:
if has(a,RootOf) then RETURN(false) fi:
if type(a,`*`) then
   for i from 1 to nops(a) do
       res:=isQM(op(i,a),vars):
       if not(res) then RETURN(false) fi
   od:
   RETURN(true)
else
   if not(has(a,vars)) then RETURN(true) fi:
   if type(a,`^`) and has(vars,op(1,a)) then
      RETURN(true)
   else
      if nops(a)=1 then
         RETURN(true)
      else
         RETURN(false)
      fi
   fi
fi:
false
end:
# isQP
# Tests if an expression is a Quasi-Polynomial.
# Synopsis
# result := isQP(expression,variables)
# Parameters
# result : a boolean valule (true or false).
# expression: a maple expression.
# variables: a set of variable names.
# Description
# Tests if a given expression is a Quasi-Polynomial in the specified variables.
# Code
isQP:=proc(a,vars)
local a2,i,res:
a2:=expand(a):
if type (a2,`+`) then
   for i from 1 to nops(a2) do
       res:=isQM(op(i,a2),vars):
       if not(res) then RETURN(false) fi
   od:
   RETURN(true)
else
   res:=isQM(a2,vars):
   RETURN(res)
fi
end:
# algsys
# Defines the dynamical system and translates it to the Lotka-Volterra form.
# Synopsis
# result := algsys(flow,varr,params)
# Parameters
# result : a list with the first element as the vector field (alist) of the associated Lotka-Volterra
#               system and the second element the list of the corresponding Quasi-Monomial variables.
# flow:  the list of the vetor flow of the system.
# varr:  the list of the phase-variables in the correponding order with flow.
# params: the set of the free parameters in flow.
# Description
# Transforms the Quasi-Polynomial dynamical system in the input into the Lotka-Volterra form.
# Code
algsys:=proc(flow,varr,params)
local i,j,prov,flin,m,n,wdym:
global SADE:
#global vars,vars2,matm,matb,mata,w,sc,parameters,qmlist
#       ,QMatA,QMatB,__cmax,__lvfield,U1,mind,nind,__addcond:
if not(type(SADE[addcond],set)) then SADE[addcond]:={} fi:
SADE[cmax]:=1:
SADE[mind]:=0:
SADE[nind]:=0:
SADE[parameters]:=params:
SADE[field]:=[flow,varr]:
SADE[_vars]:=varr:
SADE[vars2]:=varr:
flin:=expand(flow):
for i from 1 to nops(SADE[_vars]) do
    flin:=subs(SADE[_vars][i]=SADE[_vars][i](time),flin)
od:
prov:=diff(SADE[_vars][1](time),time)=flin[1]:
for i from 2 to nops(SADE[_vars]) do
    prov:=prov,diff(SADE[_vars][i](time),time)=flin[i]
od:
prov:=[prov]:
# The commented lines below are used only with NODES.
#syst:=qpods(prov):
LKform(flow,varr):
#SADE[matm]:=extendedInvariant(syst):
#SADE[matb]:=extendedExponent(syst):
#SADE[mata]:=extendedCoefficient(syst):
#SADE[mata]:=SADE[QMatA]:
#SADE[matb]:=SADE[QMatB]:
SADE[matm]:=matrix_prod(SADE[QMatB],SADE[QMatA]):
m:=linalg[rowdim](SADE[matm]):
SADE[dim]:=m:
wdym:=m:
n:=nops(flow):
i:='i':
SADE[qmlist]:=prod(varr[i]^SADE[QMatB][1,i],i=1..n):
for j from 2 to m do
    SADE[qmlist]:=SADE[qmlist],prod(varr[i]^SADE[QMatB][j,i],i=1..n)
od:
SADE[qmlist]:=[SADE[qmlist]]:
matreorg():
j:='j':i:='i':
SADE[lvfield]:=0:
for i from 1 to wdym do
    SADE[lvfield]:=SADE[lvfield]+cat(SADE[__U],1)*SADE[matm][1,i]*cat(SADE[__U],i)
od:
m:=cat(SADE[__U],1):
for i from 2 to wdym do
    prov:=0:
    for j from 1 to wdym do
        prov:=prov+cat(SADE[__U],i)*SADE[matm][i,j]*cat(SADE[__U],j)
    od:
    SADE[lvfield]:=SADE[lvfield],prov:
    m:=m,cat(SADE[__U],i)
od:
SADE[lvfield]:=[[SADE[lvfield]],[m]]
end:
# pcont
# Returns the parameters in expr.
# Synopsis
# result := pcont(expr)
# Parameters
# result : a set with the parameters in expr.
# expr: an expression.
# Description
# Returns tye parameters  in expr as defined in the global variable variables.
# Code
pcont:=proc(expr)
local i,res:
global SADE:
res:={}:
for i from 1 to nops(SADE[parameters]) do
    if has(expr,SADE[parameters][i]) then
       res:=res union {SADE[parameters][i]}
    fi
od:
res
end:
# prod
# Function prod does the same (in principle) as product, but it works.
# Synopsis
# result := prod(expr,range)
# Parameters
# result : an algebraic expression.
# expr: an algebraic expression.
# range: a range of values of a multiplication variable (like in the usual product of maple).
# Description
# prod(f(i),i=a..b) returns f(a)*f(a+1)*...*f(b-1)*f(b), with a and b integers.
# Code
prod:=proc(a,b)
local i,j,inf,sup,res,prov:
res:=1:
j:=op(1,b):
inf:=op(1,op(2,b)):
sup:=op(2,op(2,b)):
for i from inf to sup do
    prov:=subs(j=i,a):
    res:=res*prov
od:
res
end:
# matrix_prod
# Returns the matrix product of aa and bb.
# Synopsis
# result := matrix_prod(mat1,mat2)
# Parameters
# result, mat1,mat2 : a matrix array.
# Description
# Returns the matrix product of aa and bb.
# Code
matrix_prod:=proc(aa,bb)
local i,j,n,m,l,prov,k,cc:
n:=linalg[rowdim](aa):
m:=linalg[coldim](aa):
l:=linalg[coldim](bb):
cc:=array(1..n,1..l):
for i from 1 to n do
for j from 1 to l do
    prov:=0:
    for k from 1 to m do
        prov:=prov+aa[i,k]*bb[k,j]
    od:
    cc[i,j]:=prov
od
od:
cc
end:
# polyn_hom
# returns an usual homogeneous polynomial in variables vars,  of degree order.
# Synopsis
# result := polyn_hom(deg,vars)
# Parameters
# result: an algebraic expression of a homogeneous polynomial.
# deg: degree of the polynomial
# vars: list of the variables on which the polynomial will depend.
# Description
#  polyn_hom(order,vars) returns an usual homogeneous polynomial in variables vars,
# of degree order. polyn accepts a third argument even. In the later case it
# returns a polynomial with even exponents.
# Code
polyn_hom:=proc(order,vard)
local i1,i2,prov,prov2,flag:
global SADE:
if nargs=3 and args[3]=even then flag:=1 else flag:=0 fi:
prov:=1:
for i1 from 1 to nops(vard) do
     prov2:=1:
     for i2 from 1 to order do
          prov2:=prov2+op(i1,vard)^i2
     od:
     prov:=prov*prov2
od:
prov:=expand(prov):
prov2:=0;
for i1 from 1 to nops(prov) do
     if degree(op(i1,prov),vard)=order then
        if (flag=1 and type(degree(op(i1,prov),vard),even)) or flag=0 then
          prov2:=prov2+cat(SADE[_c],SADE[ccount])*op(i1,prov):
          SADE[ccount]:=SADE[ccount]+1:
        fi
     fi
od:
prov2
end:
# quasisyst
#  generates the algebraic system associated to the existence of a semi-invariant.
# Synopsis
# result := quasisyst(n,c)
# Parameters
# result: a set of equations.
# n: the degree of the quasi-polynomial
# c: OPTIONAL:
#     if booloean -> a constraint on the original variables as used in the input of algsys.
#                                  In this case a third argument is mandatory giving the set of new free
#                                  parameters introduced in the constraint.
#     if expression -> gives an ad-hoc form for the eigenvalue lamda.
# Description
# This routine generates the algebraic system associated to
# the existence of a semi-invariant. the first argument is the degree of the polynomial psi.
# If a second argument is given then the routine takes it as a constraint
# of the form variable=expression, if it is boolean,
# or a specific form for lambda, if it is an expression. If a fourth argument
# is given then it is a set of restriction conditions on the parameters of the equations.
# In the case of a constraint the third argument is the set on new free parameters.
# Code
quasisyst:=proc()
local dim,i,j,k,prov,prov2,eqs,nn:
global SADE,__ugb:
#global vars,ccount,unknowns,parameters,__psi,__lambda,grau,matm,qmlist,U1
#      ,flagchar,nind,mind,dimval,__ugb,__addcond,vars2:
SADE[addcond]:={}:
SADE[nind]:=0:
SADE[mind]:=0:
SADE[flagchar]:=0:
nn:=args[1]:
SADE[grau]:=nn:
dim:=nops(SADE[qmlist]):
SADE[_vars]:=cat(SADE[__U],1):
for i from 2 to dim do
    SADE[_vars]:=SADE[_vars],cat(SADE[__U],i)
od:
SADE[_vars]:=[SADE[_vars]]:
if nargs=2 and not(type(args[2],boolean)) then
   if ccont(args[2])={} then ccont=1 fi:
   SADE[__lambda]:=args[2]
else
   SADE[ccount]:=1:
   SADE[__lambda]:=0:
   for i from 1 to nops(SADE[_vars]) do
       SADE[__lambda]:=SADE[__lambda]+cat(SADE[_c],SADE[ccount])*SADE[_vars][i]:
       SADE[ccount]:=SADE[ccount]+1:
   od
fi:
SADE[__psi]:=polyn_hom(nn,SADE[_vars]):
prov:=semi_inv_aux([SADE[__psi],SADE[__lambda],{}]):
SADE[incognita]:=SADE[parameters]:
for i from 1 to SADE[ccount]-1 do
    SADE[incognita]:=SADE[incognita] union {cat(SADE[_c],i)}
od:
prov:=expand(prov):
prov:=final_form(prov):
if nargs>1 and (type(args[2],boolean) or type(args[2],set)) then
   prov:=numer(normal(prov)):
   prov:=subs(args[2],prov):
   prov:=subs(__ugb=1/2,expand(simp_sqrt(prov))):
   prov:=expand(normal(prov)):
   prov2:={}:
   if nargs=4 then
      for i from 1 to nops(args[4]) do
          prov2:=prov2 union {op(1,op(i,args[4]))}
      od
   fi:
   SADE[incognita]:=SADE[incognita] minus prov2:
   SADE[parameters]:=SADE[parameters] minus prov2:
   SADE[incognita]:=SADE[incognita] union args[3]:
   SADE[parameters]:=SADE[parameters] union args[3]:
   if nargs=4 then
      prov:=subs(args[4],prov):
      SADE[addcond]:=args[4] union args[2]:
   fi
fi:
eqs:=lifdec2(prov,SADE[vars2]):
eqs:=eval(eqs) minus {0}:
eqs
end:
# simp_sqrt
# simplifies an expression containing half-integer exponents of polynomials.
# Synopsis
# result := simp_sqrt(expr)
# Parameters
# result, expr: an algebraic expression.
# Description
# This routine simplifies an expression containing half-integer\
# exponents of polynomials suchs that P(x)^n/2=P(x)^(n-1)*sqrt(P(x)) .
# Code
simp_sqrt:=proc(a)
local prov,i,res,nn,rd:
global __ugb:
prov:=expand(a):
if type(prov,`+`) then
   res:=0:
   for i from 1 to nops(prov) do
       res:=res+simp_sqrt(op(i,prov))
   od:
   RETURN(res)
fi:
if type(prov,`*`) then
   res:=1:
   for i from 1 to nops(prov) do
       res:=res*simp_sqrt(op(i,prov))
   od:
   RETURN(res)
fi:
### WARNING: note that `I` is no longer of type `^`
if not(type(prov,`^`)) then RETURN(prov) fi:
nn:=op(2,prov):
rd:=op(1,prov):
if type(nn,integer) then RETURN(prov) fi:
if not(type(2*nn,integer)) then RETURN(prov) fi:
prov:=expand(rd^(nn-1/2)*__ugb):
prov:=subs(__ugb=rd^__ugb,prov):
prov
end:
# quasisolve
#
# This routine solves the algebraic system eqs for the quasi-invariant
# and return a list of sequences: the first element is psi,
# the second is lambda and the third is a set with conditions on the parameters.
# If quasisolve is invoked with one argument the algebraic system is solved
# using the standard "solve" maple routine. In that case the argument is the
# equations set to be solved. If an optional second argument is given (the equations are still
# the firts argument)  then the routine uses the Groebner package to obtain the solution.
# If the global variable SADE[nored] is set to true then quasisolve will return
# only. The default value for SADE[nored] is false.
#
quasisolve:=proc()
local res,res2,results,i,j,k,prov1,prov2,prov3,prov4,counter,term,flag,eqs
      ,numc,k2,prov1b,prov2b,prov3b,subsvar,nv:
global SADE:
#global __psi,__lambda,unknowns,ccount,parameters
#      ,__cmax,__field,flagchar,mind,nind,__nored:
eqs:=args[1]:
nv:=nops(SADE[field][2]):
eqs:=eval(eqs):
if nargs>1 then
   res:={ext_solve(eqs,SADE[incognita] union SADE[parameters],args[2])} minus {0}
else
   res:={solve(eqs,SADE[incognita] union SADE[parameters])}
fi:
res:=eval(res):
if res={} then RETURN(res) fi:
res:=arrange_solution(res,SADE[incognita],SADE[parameters]):
results:={}:
for i from 1 to nops(res) do
    prov1:=subs(res[i],eval(SADE[__psi])):
    prov2:=subs(res[i],SADE[__lambda]):
    prov3:=param_only(res[i],SADE[parameters]):
#    prov3:=op(arrsol({res[i]},SADE[parameters])):
#    prov1:=subs(prov3,eval(prov1)):
#    prov2:=subs(prov3,prov2):
    counter:=1:
# here we change __ci by _Ci
    for j from 1 to SADE[ccount]-1 do
        if has(eval(prov1),cat(SADE[_c],j)) or has(prov2,cat(SADE[_c],j)) then
           prov1:=subs(cat(SADE[_c],j)=cat(SADE[_C],counter),eval(prov1)):
           prov2:=simplify(subs(cat(SADE[_c],j)=cat(SADE[_C],counter),prov2)):
           counter:=counter+1:
           if counter > SADE[cmax] then
              SADE[cmax]:=counter
           fi
        fi
    od:
    flag:=0:
    if prov1<>0 then
       prov4:=C_Ccont(prov1):
       numc:=nops(prov4):
       res2:={}:
       flag:=0:
       for k from 1 to numc do
           prov1b:=simplify(expand(eval(prov1))):
           prov2b:=simplify(expand(prov2)):
           for k2 from 1 to numc do
               subsvar:=op(k2,prov4):
               if k=k2 then
                  prov1b:=traperror(eval(subs(subsvar=1,eval(prov1b)))):
                  prov2b:=traperror(eval(subs(subsvar=1,prov2b))):
               else
                  prov1b:=traperror(eval(subs(subsvar=0,eval(prov1b)))):
                  prov2b:=traperror(eval(subs(subsvar=0,prov2b))):
               fi
           od:
           if prov1b<>lasterror and prov2b<>lasterror then
              res2:=res2 union {[arrayfactor(evalm(prov1b)),factor(prov2b),factor(prov3)]}
           else
              flag:=1
           fi
       od:
       if flag=0 then
          results:=results union res2
       else
          results:=results union{[arrayfactor(evalm(prov1)),factor(prov2),factor(prov3)]}
       fi:
       if numc=0 then
          results:=results union {[arrayfactor(evalm(prov1),nv),factor(prov2),factor(prov3)]}
       fi
    fi
od:
if (SADE[mind]=0 and SADE[nind]=0) and SADE[nored] then
   results:=clean_all(results)
fi:
if SADE[mind]>0 or SADE[nind]>0 then
   prov1:={}:
   for i from 1 to nops(results) do
       if setcont(results[i][1],SADE[field][2])<>{} then
          prov1:=prov1 union {results[i]}
       fi
   od:
   results:=prov1
fi:
if has(results,RootOf) then
   prov1:={}:
   results:={allvalues(results)}:
   for i from 1 to nops(results) do
       prov1:=prov1 union results[i]
   od:
   results:=prov1
fi:
results
end:
# paramcont
# Returns a list with the parameters found in expr.
# Synopsis
# result := paramcont(expr)
# Parameters
# result: a list with the parameters in expr as defined by the global varaible parameters.
# expr: any expression of maple.
# Description
# Returns a list with the parameters found in expr.
# Code
paramcont:=proc(expr)
local i,res:
global SADE:
res:={}:
for i from 1 to nops(SADE[parameters]) do
    if has(expr,SADE[parameters][i]) then
       res:=res union {SADE[parameters][i]}
    fi
od:
res
end:
# ccont
# Returns a list with the __c.i in expr.
# Synopsis
# result := ccont(expr)
# Parameters
# result: a set with the variables __c.i in expr.
# expr: any expression.
# Description
# Returns a list with the __c.i in expr.
# Code
ccont:=proc(expr)
local i,res:
global SADE:
res:={}:
for i from 1 to SADE[ccount]-1 do
    if has(expr,cat(SADE[_c],i)) then
       res:=res union {cat(SADE[_c],i)}
    fi
od:
res
end:
# C_Ccont
#  Returns a set with the constants SADE[_C]||i  in expr.
# Synopsis
# result := C_Ccont(expr)
# Parameters
# result: a set with the variables _C.i in expr.
# expr: any expression.
# Description
# Returns a set with the constants _C.i in expr.
# The global variable __cmax is an integer  which controls the maximum number
# of _C.i constants to search.
# Code
C_Ccont:=proc(expr)
local i,res:
global SADE:
#global __cmax:
res:={}:
for i from 1 to SADE[cmax] do
    if has(eval(expr),cat(SADE[_C],i)) then
       res:=res union {cat(SADE[_C],i)}
    fi
od:
res
end:
# Ucont
#  Returns a set with the variables U.i in expr.
# Synopsis
# result := Ucont(expr)
# Parameters
# result: a set with the variables U.i in expr.
# expr: any expression.
# Description
# Returns a set with the variables U.i in expr. The range of i is given by the number of elements
# in the global variable qmlist.
# Code
Ucont:=proc(expr)
local i,res:
global SADE:
res:={}:
for i from 1 to nops(SADE[qmlist]) do
    if has(expr,cat(SADE[__U],i)) then
       res:=res union {cat(SADE[__U],i)}
    fi
od:
res
end:
# xcont
# Returns a set with the original variables in expr, as defined in the input of algsys.
# Synopsis
# result := xcont(expr)
# Parameters
# result: a set with the original variables in expr.
# expr: any expression.
# Description
# Returns a set with the variables U.i in expr. The range of i is given by the number of elementsReturns a set with the original variables in expr, as defined in the input of algsys and given by the global
# variable vars2.
# Code
xcont:=proc(expr)
local i,res:
global SADE:
res:={}:
for i from 1 to nops(SADE[vars2]) do
    if has(expr,SADE[vars2][i]) then
       res:=res union {SADE[vars2][i]}
    fi
od:
res
end:
# invsearch
# Takes the output of quasisolve and returns all possible invariants as a set of lists.
# Synopsis
# result := invsearch(a)
# Parameters
# result: a set of lists, each list has the invariant and the conditions on the free parameters.
# a: a set of semi-invariants as given by the output of quasisolve.
# Description
# This routine takes the output of quasisolve and returns all possible
# invariants as a set of lists. the first element of the list is the
# invariant and the second the conditions on the parameters for these invariants.
# Code
invsearch:=proc(qs)
local i,j,k,res,prov,cond,cond2,inv:
#global qmlist,parameters:
global SADE:
res:={}:
prov:=qs:
for j from 1 to nops(prov) do
    for i from j+1 to nops(prov) do
        if prov[j][2]=prov[i][2] then
           inv:=simplify(prov[j][1]/prov[i][1]):
           cond:=prov[j][3] union prov[i][3]:
           if Ucont(inv)<>{} then
              for k from 1 to nops(SADE[qmlist]) do
                  inv:=expand(subs(cat(SADE[__U],k)=SADE[qmlist][k],inv)):
                  inv:=traperror(simplify(subs(cond,inv))):
                  if inv<>lasterror then
                     inv:=simplify(inv)
                  fi
              od:
              if xcont(inv)<>{} then
                 cond:=solve(cond,SADE[parameters]):
                 cond2:={}:
                 for k from 1 to nops(cond) do
                     if op(1,cond[k])<>op(2,cond[k]) then
                        cond2:=cond2 union {cond[k]}
                     fi
                 od:
                 inv:=traperror(subs(cond2,inv)):
                 if xcont(inv)<>{} then
                    res:=res union {[inv,cond2]}
                 fi
              fi
           fi
        fi
    od
od:
res
end:
# cleansolve
# Eliminates from a list of semi-invariants all quasi- monomials.
# Synopsis
# result := cleansolve(a)
# Parameters
# result: a set of semi-invariants.
# a: a set of semi-invariants.
# Description
# This routine eliminates from the list aa the elements which correspond to monomial semi-invariants.
# aa is in the form of the output of quasisolve.
# Code
cleansolve:=proc(aa)
local res,i,prov:
res:={}:
for i from 1 to nops(aa) do
# Aqui corrigi um erro da versao 1.0 na qual faltava o expand.
     prov:=expand(aa[i][1]):
     if type(prov,`+`) then
        res:=res union {aa[i]}
     fi
od:
res
end:
# cleansolution
# Eliminates the factorizable semi-invariants.
# Synopsis
# result := cleansolution(a)
# Parameters
# result: a set of semi-invariants.
# a: a set of semi-invariants.
# Description
# This routine eliminates from the list a the elements which corresponds to
# factorizable semi-invariants.
# Code
cleansolution:=proc(aa)
local bb,prov,prov2,i,j,cc,nn,dd:
cc:={}:
bb:=factor(aa):
for i from 1 to nops(bb) do
    prov:=bb[i][1]:
    if type(prov,`*`) then
       nn:=0:
       for j from 1 to nops(prov) do
           if Ucont(op(j,prov))<>{} then
              nn:=nn+1
           fi
       od:
       if nn=1 then
          prov2:=1:
          for j from 1 to nops(prov) do
              if Ucont(op(j,prov))<>{} then
                 prov2:=prov2*op(j,prov)
              fi
          od:
          cc:=cc union {[prov2,bb[i][2],bb[i][3]]}
       fi
    else
       cc:=cc union {[prov,bb[i][2],bb[i][3]]}
    fi
od:
dd:={}:
for i from 1 to nops(cc) do
### WARNING: note that `I` is no longer of type `^`
    if not(type(cc[i][1],`^`)) then
       dd:=dd union {[cc[i][1],cc[i][2],cc[i][3]]}
    fi
od:
dd
end:
# clean_all
# Applies  cleansolve  to all solutions.
# Synopsis
# result := clean_all(a)
# Parameters
# result: a set of semi-invariants.
# a: a set of semi-invariants.
# Description
# Applies both cleansolve.
# Code
clean_all:=proc(aa)
local res,resfin,i,prov1:
global SADE:
res:=cleansolve(aa):
resfin:={}:
for i from 1 to nops(res) do
    prov1:=subs(res[i][3],res[i][1]):
    prov1:=collect(prov1,C_Ccont(prov1)):
    resfin:=resfin union {[prov1,subs(res[i][3],res[i][2]),res[i][3]]}
od:
if 
SADE[grau]=1 then
   resfin:=resfin union {[1,0,{}]}
fi:
resfin
end:
# final_form
#
# Rewrites an expression in terms of the original variables as defines in algsys and stored
#in the global variable vars2. All LV Quasi-Monomials U.i are replaced by their original expressions
#
final_form:=proc(aa)
local i,res,res2,prov,nv:
#global qmlist,vars2,__field:
global SADE:
nv:=nops(SADE[field][2]):
res:=aa:
for i from 1 to nops(SADE[qmlist]) do
    res:=subs(cat(SADE[__U],i)=op(i,SADE[qmlist]),res)
od:
res:=expand(res):
if type(res,set) then
   res2:={}:
   for i from 1 to nops(res) do
       prov:=op(i,res):
       if setcont(prov,SADE[vars2])<>{} then
          res2:=res2 union {prov}
       fi
   od
else
   res2:=res
fi:
if nargs=2 then
   res:={}:
if type(res2[1][1],array) then
   for i from 1 to nops(res2) do
       res:=res union {[convert(arraysimplify(res2[i][1],nv),array),res2[i][2]]}
   od
else
   for i from 1 to nops(res2) do
       res:=res union {[simplify(res2[i][1],assume=real),res2[i][2]]}
   od
fi
else
   RETURN(res2)
fi:
res
end:
# test_constcoeff
# Test a system a set or a list of polynomial for constant coefficients.
# Synopsis
# result:=test_constcoeff(eqs,vars)
# Parameters
# result: a boolean variable (true or false).
# eas: a set or a list of multivariante polynomials.
# vars: a set or a lista of variable names.
# Description
# Tests the set or list of multivariate polynomials in the variables vars eqs for constant coefficients.
# Code
test_constcoeff:=proc(eqs,vars)
local i,j,prov:
for i from 1 to nops(eqs) do
    prov:={coeffs(expand(eqs[i]),{op(vars)})}:
    for j from 1 to nops(prov) do
       if not(type(prov[j],constant)) then
          RETURN(false)
       fi
    od
od:
true
end:
# ext_solve
#
# This routine solves an algebraic system by first reducing it to its Groebner basis.
# The syntax is the same as the usual solve.
#
ext_solve:=proc(eqs,vars,oa)
local i,res,prov,prov2,cf:
global SADE:
prov:=Groebner[Basis](eqs,plex(op(vars))):
res:={solve({op(prov)},vars)}:
op(res)
end:
# moncoeff
# Return the coefficient of a given quasi-monomial in a quasi-polynomial .
# Synopsis
# result := moncoeff(a,mon,varbls)
# Parameters
# result: an expression.
# a: a quasipolynomial.
# mon: a quasi-monomial.
# varbls: a set of variables.
# Description
# This routine returns the coefficient of the quas-monomial mon in the quasi-polynomial
# a in the variables varbls.
# Code
moncoeff:=proc(a,mon,varbls)
local nn,i,prov,aa,res:
aa:=expand(a):
if type(aa,`+`) then
   nn:=nops(aa)
else
   nn:=1
fi:
res:=0:
for i from 1 to nn do
    if nn=1 then
       prov:=aa
    else
       prov:=op(i,aa)
    fi:
    prov:=simplify(prov/mon):
    if setcont(prov,varbls)={} then res:=res+prov fi
od:
res
end:
# newfactor
#  Rearranges an expression such that all exponents of each variable are collected as a single exponent.
# Synopsis
# result := newfactor(a,v)
# Parameters
# result: an algebraic expressions.
# a: an algebraic expression.
# v: a set of variables.
# Description
# Rearranges an expression such that all exponents of each variable in the set v are collected
# as a single exponent.
# Code
newfactor:=proc(a,vars)
local b,prov,prov2,prov3,pwrs,rpc,i:
pwrs:=array(1..nops(vars)):
for i from 1 to nops(vars) do
      pwrs[i]:=0
od:
b:=expand(a):
if not(type(b,`*`)) then RETURN(a) fi:
prov:=1:
rpc:=1:
for i from 1 to nops(b) do
      prov2:=op(i,b):
      if setcont(prov2,vars)<>{} then
         if type(prov2,`^`) then
            prov3:=op(2,prov2):
            prov2:=op(1,prov2):
            if type(prov2,`^`) then
               prov3:=prov3*op(2,prov2):
               prov2:=op(1,prov2)
            fi
         else
            prov3:=1:
         fi:
         pwrs[varblspos(prov2,vars)]:=evalm(pwrs[varblspos(prov2,vars)])+prov3
     else
         rpc:=rpc*prov2
     fi
od:
for i from 1 to nops(vars) do
      rpc:=rpc*vars[i]^evalm(pwrs[i])
od:
rpc
end:
# varblspos
#
# Returns the position of a given variable in var in a list of variables in varbls.
#
varblspos:=proc(var,varbls)
local i:
for i from 1 to nops(varbls) do
    if op(i,varbls)=var then RETURN(i) fi
od
end:
# LKform
# Computes the Lotka-Volterra matrices A and B.
# Synopsis
# result := LKform(syst,varbls)
# Parameters
# result: null.
# syst: a list containing the equations.
# varbls: a list containing the variables in the respective order to syst.
# Description
#  Computes the matrix A (the coefficient matrix)  in the global variable QMatA
# and the matrix B (exponents matrix) put in the global variable QMatB for the system of
# ODE's in the sequence syst with the variables in the sequence vars, for the purely quadratic
# Lotka-Volterra form.
# Code
LKform:=proc(syst,varbls)
local nn,mm,nummon,ll,monom,i,j,k,prov,prov2,prov3,termo:
#global QMatA,QMatB:
global SADE:
nn:=nops(syst):
monom:={}:
for i from 1 to nn do
    prov:=expand(syst[i]/varbls[i]):
    eqlst||i:=prov:
    if type(prov,`+`) then
       mm:=nops(prov)
    else
       mm:=1
    fi:
    for j from 1 to mm do
        if mm>1 then
           termo:=op(j,prov)
        else
           termo:=prov
        fi:
        if type(termo,`*`) and setcont(termo,varbls)<>{} then
           ll:=nops(termo)
        else
           ll:=1
        fi:
        if ll=1 then
           if setcont(termo,varbls)={} then
              monom:=monom union {1}
           else
              monom:=monom union {termo}
           fi
        else
           prov2:=1:
           for k from 1 to ll do
               prov3:=op(k,termo):
               if setcont(prov3,varbls)<>{} then
                  prov2:=prov2*prov3
               fi
           od:
           prov2:=newfactor(prov2,varbls):
           monom:=monom union {prov2}
        fi
    od
od:
monom:=[op(monom)]:
nummon:=nops(monom):
SADE[QMatA]:=array(1..nn,1..nummon):
SADE[QMatB]:=array(1..nummon,1..nn):
for i from 1 to nn do
for j from 1 to nummon do
    prov:=eqlst||i:
    SADE[QMatA][i,j]:=moncoeff(prov,monom[j],varbls)
od
od:
for i from 1 to nummon do
    for j from 1 to nn do
        SADE[QMatB][i,j]:=0
    od:
    if monom[i]<>1 then
    if type(monom[i],`*`) then
       ll:=nops(monom[i])
    else
       ll:=1
    fi:
    for j from 1 to ll do
        if ll=1 then
           prov:=newfactor(monom[i],varbls)
        else
           prov:=newfactor(op(j,monom[i]),varbls)
        fi:
### WARNING: note that `I` is no longer of type `^`
        if type(prov,`^`) then
           prov2:=op(1,prov):
           prov3:=op(2,prov)
        else
           prov2:=prov:
           prov3:=1
        fi:
        prov2:=varblspos(prov2,varbls):
        SADE[QMatB][i,prov2]:=prov3
    od
    fi
od:
end:
# numterm
# Return the numer of terms in an expression of type `+`.
# Synopsis
# result := numterm(a)
# Parameters
# result: an integer.
# a: aan algebraic expression.
# Description
# Return the numer of terms in an expression of type `+`. In there is no sum in the expression,
# then the routine counts only one term.
# Code
numterm:=proc(aa)
if type(aa,`+`) then RETURN(nops(aa)) fi:
1
end:
# cont
# Logical test for a set to be a sub-set of another set.
# Synopsis
# result := cont(a,b)
# Parameters
# result: a boolean, true or false.
# a,b: a set.
# Description
#  Returns true if the set b is a subset of a, and returns false otherwise.
# Code
cont:=proc(a,b)
local i:
if nops(b)>nops(a) then RETURN(false) fi:
for i from 1 to nops(b) do
        if not(member(op(i,b),a)) then RETURN(false) fi
od:
true
end:
# LieDeriv
# Computes the Lie derivative of a tensor.
# Synopsis
# result := LieDeriv(TT,VV,n,m,vars)
# Parameters
# result: an array.
# TT: a tensor represented by an array.
# VV: a vector array.
# n,m: integers.
# vars: a set of variables.
# Description
# Returns the Lie derivative of the tensor TT of kind (n,m) with respect
# to the vector field VV, with components as functions of variables in vars.
# Code
LieDeriv:=proc(TT,VV,n,m,vars)
local dimen,prov,prov2,i,k,ups,downs,dimext,downs2,k1,k2,res,ups2,UU
      ,ub,db:
dimen:=nops(vars):
dimext:=1..dimen:
prov:=dimext:
for i from 2 to n+m do
    prov:=prov,dimext
od:
dimext:=prov:
UU:=array(dimext):
for i from 1 to dimen^(n+m) do
    ups:=nuplesequence(i,n+m,dimen):
# Change the next two lines for MapleV Release 3 with the two commented
# lines below.
#    downs:=ups[n+1..n+m]:
#    ups:=ups[1..n]:
    downs:=op(ups[n+1..n+m]):
    ups:=op(ups[1..n]):
    res:=0:
    for k from 1 to dimen do
        prov2:=ups,downs:
        prov2:=eval(diff(eval(TT[prov2]),vars[k])):
        res:=res+VV[k]*prov2
    od:
    for k from 1 to dimen do
        for k1 from 1 to m do
            if k1=1 then
               downs2:=k
            else
               downs2:=op(1,[downs])
            fi:
            for k2 from 2 to m do
                if k1=k2 then
                   downs2:=downs2,k
                else
                   downs2:=downs2,op(k2,[downs])
                fi
            od:
            db:=[downs]:
            res:=res+diff(VV[k],vars[db[k1]])*TT[ups,downs2]
        od
    od:
    for k from 1 to dimen do
        for k1 from 1 to n do
            if k1=1 then
               ups2:=k
            else
               ups2:=op(1,[ups])
            fi:
            for k2 from 2 to n do
                if k1=k2 then
                   ups2:=ups2,k
                else
                   ups2:=ups2,op(k2,[ups])
                fi
            od:
            ub:=[ups]:
            res:=res-diff(VV[ub[k1]],vars[k])*TT[ups2,downs]
        od
    od:
    UU[ups,downs]:=res
od:
UU
end:
# nuplesequence
# Returns the k-th n-uple of indices ranging from 1 to m.
# Synopsis
# result := nuplesequence(k,n,m)
# Parameters
# result: a list.
# k,n,m: integers.
# Description
# Returns the k-th n-uple of indices ranging from 1 to m.
# Code
nuplesequence:=proc(kk,n,m)
local nuple,rest,prov,i,k:
k:=kk-1:
if kk>m^n or kk<1 then RETURN() fi:
nuple:=trunc(k/m^(n-1)):
rest:=k-nuple*m^(n-1):
nuple:=nuple+1:
for i from 2 to n do
    prov:=trunc(rest/m^(n-i)):
    nuple:=nuple,prov+1:
    rest:=rest-prov*m^(n-i)
od:
nuple:=[nuple]:
nuple
end:
# tensordeteq
# Returns the determining equations for the semi-invariant Tensors.
# Synopsis
# result := tensordeteq(n,m,deg)
# Parameters
# result: a set of equations.
# n,m,deg: integers.
# Description
# Returns the determining equations for the semi-invariant Tensors
# of kind  (m,n) in the original variables, for a polynomial tensor of order deg in the
# Lotka-Volterra variables.
# Code
tensordeteq:=proc(n,m,deg)
local dimext,dimen,TT,i,j,ind,VV,eqs,UU,prov,prov2,nvxi,lmb,flag,nv:
#global ccount,matm,qmlist,unknowns,__lambda,__psi,U1,nind,mind,flagchar,dimval,__field,vars2:
global SADE:
SADE[flagchar]:=1:
nv:=nops(SADE[field][2]):
SADE[nind]:=n:
SADE[mind]:=m:
SADE[_vars]:=cat(SADE[__U],1):
for i from 2 to nops(SADE[qmlist]) do
    SADE[_vars]:=SADE[_vars],cat(SADE[__U],i)
od:
SADE[_vars]:=[SADE[_vars]]:
dimen:=nops(SADE[_vars]):
SADE[dimval]:=dimen:
dimext:=1..dimen:
SADE[ccount]:=1:
for i from 2 to n+m do
    dimext:=dimext,1..dimen
od:
TT:=array(dimext):
UU:=array(dimext):
for i from 1 to dimen^(n+m) do
    ind:=op(nuplesequence(i,n+m,dimen)):
    prov:=polyn_hom(deg,SADE[_vars]):
    TT[ind]:=prov
od:
SADE[__psi]:=TT:
VV:=array(1..dimen):
SADE[_vars]:=cat(SADE[__U],1):
for i from 2 to nops(SADE[qmlist]) do
    SADE[_vars]:=SADE[_vars],cat(SADE[__U],i)
od:
SADE[_vars]:=[SADE[_vars]]:
for i from 1 to dimen do
    VV[i]:=0:
    for j from 1 to dimen do
        VV[i]:=VV[i]+cat(SADE[__U],i)*SADE[matm][i,j]*cat(SADE[__U],j)
    od
od:
UU:=LieDeriv(TT,VV,n,m,SADE[_vars]):
SADE[__lambda]:=0:
for i from 1 to dimen do
    SADE[__lambda]:=SADE[__lambda]+cat(SADE[_c],SADE[ccount])*cat(SADE[__U],i):
    SADE[ccount]:=SADE[ccount]+1
od:
eqs:={}:
UU:=coordtr(UU,n,m):
TT:=coordtr(TT,n,m):
lmb:=final_form(SADE[__lambda]):
SADE[__psi]:=TT:
for i from 1 to dimen^(n+m) do
    ind:=op(nuplesequence(i,n+m,dimen)):
    flag:=0:
    prov:=[ind]:
# Here we impose the requirement that the tensor TT belongs to the
# hypersurface of the quasi-monomial space defining the original space.
    for j from 1 to nops(prov) do
        if prov[j]>nv then
           flag:=1
        fi
    od:
    if flag=1 then
       eqs:=eqs union{UU[ind],TT[ind]}
    else
       UU[ind]:=UU[ind]-lmb*TT[ind]:
       eqs:=eqs union {UU[ind]}
    fi
od:
SADE[incognita]:={}:
for i from 1 to SADE[ccount]-1 do
    SADE[incognita]:=SADE[incognita] union {cat(SADE[_c],i)}
od:
prov:={}:
for i from 1 to nops(eqs) do
# Here we modified with respect to version 1.0
    prov2:=final_form(expand(eqs[i])):
    prov2:=lifdec2(prov2,SADE[vars2]):
    prov:=prov union prov2
od:
eqs:=prov:
eqs
end:
# invariant_tensor
# Returns the invariant tensor fields from the semi-invariant tensors.
# Synopsis
# result := invariant_tensor(res)
# Parameters
# result: a set of lists.
# res: a set of lists.
# Description
# Given the output of tensordeteq this routine returns the invariant tensor fields of kind n,m.
# Code
invariant_tensor:=proc(res)
local i,resultd,lamb,lineqs,tensr,j,k,prov,prov2,unk,dimen,dimext,UU,ind,n,m,flag,r:
#global qmlist,matm,U1,tt,U,nind,mind,__field:
global SADE:
n:=SADE[nind]:
m:=SADE[mind]:
dimen:=nops(SADE[field][2]):
dimext:=1..dimen:
for i from 2 to n+m do
    dimext:=dimext,1..dimen
od:
UU:=array(dimext):
resultd:={}:
for i from 1 to  nops(res) do
    tensr:=eval(op(1,res[i])):
    lamb:=op(2,res[i]):
    lineqs:={}:
    flag:=0:
    for k from 1 to dimen^(n+m) do
        ind:=op(nuplesequence(k,n+m,dimen)):
        if tensr[ind]<>0 then
           flag:=1
        fi
    od:
    if flag=1 then
       unk:={}:
       for j from 1 to nops(SADE[qmlist]) do
           prov:=0:
           for k from 1 to nops(SADE[qmlist]) do
               prov:=prov+SADE[matm][k,j]*cat(SADE[_tt],k)
           od:
           unk:=unk union {cat(SADE[_tt],j)}:
           lineqs:=lineqs union {prov+coeff(expand(lamb),cat(SADE[__U],j))}
       od:
       lineqs:=subs(res[i][3],lineqs):
       unk:=unk union C_Ccont(lineqs):
       lineqs:=solve(lineqs,unk):
       if lineqs<>{} and {lineqs}<>{} then
          prov:=cat(SADE[__U],1)^cat(SADE[_tt],1):
          for j from 2 to nops(SADE[qmlist]) do
              prov:=eval(prov*(cat(SADE[__U],j))^cat(SADE[_tt],j))
          od:
          prov:=subs(lineqs,prov):
          prov:=final_form(prov):
          for k from 1 to dimen^(n+m) do
              ind:=op(nuplesequence(k,n+m,dimen)):
              prov2:=eval(subs(lineqs,eval(tensr[ind]))):
              UU[ind]:=prov*prov2
          od:
          prov:=traperror(evalm(subs(op(3,res[i]),evalm(UU)))):
          if prov<>lasterror then
             resultd:=resultd union {[evalm(prov),op(3,res[i])]}
          fi
       fi
    fi
od:
r:={}:
for i from 1 to nops(resultd) do
    prov:=resultd[i]:
    j:=1:
    for k from 1 to nops(SADE[qmlist]) do
        if has(prov,cat(SADE[_tt],k)) then
           prov:=subs(cat(SADE[_tt],k)=cat(_C,j),prov):
           j:=j+1
        fi
     od:
     r:=r union {prov}
od:
RETURN(r)
end:
# QPsymmetries
#
# Obtains the Quasi-Polynomial symmetry generators for first order Quasi-Polynomial
# system and the corresponding existence conditions on the parameters.
#
QPsymmetries:=proc()
local i,j,eq,prov,prov2,vars,res,n:
global SADE:
LVformat(args[1..nargs-1]):
n:=args[nargs]:
eq:=tensordeteq(1,0,n):
prov:=quasisolve(eq):
prov:=invariant_tensor(prov):
res:={}:
vars:=SADE[field][2]:
for i from 1 to nops(prov) do
    prov2:=0:
    for j from 1 to nops(vars) do
        prov2:=prov2+prov[i][1][j]*D[vars[j]]
    od:
    res:=res union {[prov2,prov[i][2]]}
od:
res
end:
# arrayfactor
# Factorizes the elements of an array.
# Synopsis
# result := arrayfactor(A)
# Parameters
# result:an array.
# A: an array.
# Description
# This routine factorizes the elements of the array A.
# Code
arrayfactor:=proc(UU)
local prov,i,VV,dimext,dim:
#global nind,mind,vars:
global SADE:
dim:=nops(SADE[_vars]):
if not(type(UU,array)) then
   RETURN(factor(UU))
fi:
if SADE[nind]=0 and SADE[mind]=0 then
   factor(UU):
   RETURN(UU)
fi:
dimext:=1..dim:
prov:=dimext:
for i from 2 to SADE[nind]+SADE[mind] do
    prov:=prov,dimext
od:
dimext:=prov:
VV:=array(dimext):
for i from 1 to dim^(SADE[nind]+SADE[mind]) do
    prov:=op(nuplesequence(i,SADE[nind]+SADE[mind],dim)):
    VV[prov]:=factor(evalm(UU[prov]))
od:
evalm(VV)
end:
# arraysimplify
# Simplifies the elements of an array.
# Synopsis
# result := arraysimplify(A,dim)
# Parameters
# result: an array.
# A: an array.
# dim: an integer.
# Description
# This routine simplifies the elements of the array A of dimension dim.
# Code
arraysimplify:=proc(UU,dim)
local prov,i,VV,dimext:
#global nind,mind:
global SADE:
if not(type(UU,array)) then
   RETURN(factor(UU))
fi:
if SADE[nind]=0 and SADE[mind]=0 then
   simplify(UU):
   RETURN(UU)
fi:
dimext:=1..dim:
prov:=dimext:
for i from 2 to SADE[nind]+SADE[mind] do
    prov:=prov,dimext
od:
dimext:=prov:
VV:=array(dimext):
for i from 1 to dim^(SADE[nind]+SADE[mind]) do
    prov:=op(nuplesequence(i,SADE[nind]+SADE[mind],dim)):
    VV[prov]:=simplify(evalm(UU[prov]),assume=real)
od:
evalm(VV)
end:
# inv_verif
# Verifies a set of invariants.
# Synopsis
# result := inv_verif(aa,time)
# Parameters
# result: null.
# aa: a set of invariants.
# time: a variable name.
# Description
# This routine verifies for the invariants in the list aa, with respect
# to the vector field and variables defined in the routine algsys.
# Code
inv_verif:=proc(aa,time)
local i,j,prov,res,gg,ff,vv:
#global __field,__addcond:
global SADE:
ff:=SADE[field][1]:
vv:=SADE[field][2]:
for i from 1 to nops(aa) do
      if SADE[addcond]<>{} then
         prov:=traperror(subs(aa[i][2],subs(SADE[addcond],aa[i][1])))
      else
         prov:=aa[i][1]
      fi:
      if SADE[addcond]<>{} then
         gg:=subs(SADE[addcond],ff)
      else
         gg:=ff
      fi:
      gg:=subs(aa[i][2],gg):
      res:=0:
      for j from 1 to nops(vv) do
            res:=res+diff(prov,vv[j])*gg[j]
      od:
      res:=res+diff(prov,time):
      if SADE[addcond]<>{} then
         res:=subs(SADE[addcond],res)
      fi:
         if prov<>lasterror then
            print(i,simplify(res))
         else
            print(i,lasterror)
         fi
      #fi
od
end:
# semi_inv_verif
# Verifies a set of semi-invariants.
# Synopsis
# result := semi_inv_verif(a)
# Parameters
# result: null.
# a: a set of lists..
# Description
#  This routine verifies for the semi-invariants in aa as given by the output of quasisolve.
# Code
semi_inv_verif:=proc(aa)
local i,j,k,p,l,c,r:
for i from 1 to nops(aa) do
    r:=semi_inv_aux(aa[i]):
    print(i,r):
od:
end:
# semi_inv_aux
# Verifies a single semi-invariant.
# Synopsis
# result := semi_inv_aux(a)
# Parameters
# result: an algebraic expression.
# a: a list.
# Description
# Verifies a singles semi-invariant (typically an element of the list output of quasi-solve),
# and returns the expressions for der(psi,t)-lambda*psi, wher lambda is the eigenvalue
# and psi the semi-invariant. The correct values should be zero.
# Code
semi_inv_aux:=proc(aa)
local p,l,c,r,j,k:
#global matm,qmlist,__addcond:
global SADE:
p:=aa[1]:
l:=aa[2]:
c:=aa[3]:
r:=0:
for j from 1 to nops(SADE[qmlist]) do
for k from 1 to nops(SADE[qmlist]) do
    r:=r+diff(p,cat(SADE[__U],j))*cat(SADE[__U],j)*SADE[matm][j,k]*cat(SADE[__U],k)
od
od:
r:=normal(final_form(subs(c,simplify(r-l*p)))):
if SADE[addcond]<>{} then
   r:=subs(SADE[addcond],r):
   r:=subs(c,r):
   r:=simplify(r)
fi:
r
end:
# take_out
# Eliminates the elements containing a condition in a specified set or with a vanishing
# invariant or semi-invariant.
# Synopsis
# result := take_out(a,s)
# Parameters
# result: a set
# a: a set.
# s: a boolean condition or a set of boolean conditions.
# Description
# Eliminates in the set aa all the elements containing any of the
# conditions in rule and wiht a vanishing semi-invariant.
# Code
take_out:=proc(aa,rule)
local i,j,res,res2:
#res2:=final_form(aa):
res2:=aa:
for i from 1 to nops(rule) do
    res:={}:
    for j from 1 to nops(res2) do
        if not(has(res2[j],rule[i])) then
           res:=res union {res2[j]}
        fi
    od:
    res2:=res
od:
res:={}:
for i from 1 to nops(res2) do
    if res2[i][1]<>0 then
       res:=res union {res2[i]}
    fi
od:
res
end:
# general_poly
# Returns a generalized homogeneous polynomial.
# Synopsis
# result := general_poly(homdeg,maxdeg,vars)
# Parameters
# result: an algebraic exrpession.
# homdeg: an integer.
# maxdeg: an integer.
# vars: a set.
# Description
# Returns a generalized homogeneous polynomial in a given set of variables of given order and
# range of negative exponents in the polynomial. The first argument is the order of the polynomial,
# the second one the range of negative exponents in the polynomial and the third one the set of
# variables on which the expansion is performed to form the polynomial.
# Code
general_poly:=proc(homdeg,maxdeg,vars)
local res,res2,prov,i,vars2:
global SADE:
vars2:={op(vars)}:
res:=genmonom(-maxdeg,homdeg+maxdeg,vars):
res2:=0:
for i from 1 to nops(res) do
    prov:=op(i,res):
    if degree(prov,vars2)=homdeg then
       res2:=res2+prov
    fi
od:
res:=0:
for i from 1 to nops(res2) do
    res:=res+cat(c,SADE[ccount])*op(i,res2):
    SADE[ccount]:=SADE[ccount]+1
od:
res
end:
# genmonom
# Returns a sum of generalized monomials with a given range for the exponents of each variable.
# Synopsis
# result := genmonom(n,m,vars)
# Parameters
# result: an algebraic exrpession.
# n: an integer.
# m: an integer.
# vars: a set of variables.
# Description
#  Returns a sum of generalized monomials with a given range for the exponents of each variable.
# The first argument is the lower bound and the second argument the upper bound for the range of
# the exponents of the monomials. The third argument is the set of varibles on which the monomials
# depend.
# Code
genmonom:=proc(n,m,vars)
local outp,vars2,i,k,res,npp:
outp:=1:
vars2:=vars:
while vars2<>{} do
      res:=0:
      npp:=nops(outp):
      for i from 1 to npp do
          for k from n to m do
              res:=res+op(i,outp)*vars2[1]^k
          od
      od:
      outp:=res:
      if nops(vars2)=1 then
         vars2:={}
      else
         vars2:=[vars2[2..nops(vars2)]]
      fi
od:
outp
end:
# newquasisyst
# Generates the algebraic system associated to the existence of a semi-invariant of a general homogeneous system.
# Synopsis
# result := newquasisyst(eqsb,varsb,homdeg,m,params,nome)
# Parameters
# result: a set of equations
# eqsb: a list of equations.
# varsb: a list of variable names.
# homdeg: an integer
# m: an integer.
# params: a set of variable names.
# nome:  a variable name.
# Description
# Generates the algebraic system associated to the existence of a semi-invariant of a QP
# system of ODE's. The first argument is the list with the equations, the second one
# is the list with the corresponding variables, the third is the order of the semi-invariant, the
# fourth is the order of the semi-invariant, the fifth is the set of free parameters in the equations
# and the sixth is a variable name used to homegenize the system.
# Code
newquasisyst:=proc(eqsb,varsb,homdeg,m,params,nnome)
local psidot,res,i,detsyst,vars3,nn,eqs,varss:
#global vars2,ccount,__psi,__lambda,parameters,unknowns,matm,walsyst,__nome,__cmax:
global SADE:
SADE[vars2]:=varsb:
SADE[cmax]:=1:
SADE[nome]:=nnome:
SADE[ccount]:=1:
eqs:=homog_poly_syst(eqsb,varsb,nnome):
varss:=eqs[2]:
eqs:=eqs[1]:
SADE[walsyst]:=[eqs,varss]:
vars3:={op(varss)}:
SADE[matm]:={}:
nn:=0:
for i from 1 to nops(eqs) do
    if degree(eqs[i],vars3)>nn then
       nn:=degree(eqs[i],vars3)
    fi
od:
SADE[parameters]:=params:
SADE[incognita]:=params:
SADE[ccount]:=1:
SADE[__psi]:=general_poly(homdeg,0,varss):
SADE[__lambda]:=general_poly(nn-1,m,varss):
psidot:=0:
for i from 1 to nops(varss) do
    psidot:=psidot+diff(SADE[__psi],varss[i])*eqs[i]
od:
res:=psidot-SADE[__lambda]*SADE[__psi]:
res:=expand(res):
detsyst:=lifdec2(res,varss):
detsyst:=eval(detsyst):
for i from 1 to gera[ccount]-1 do
    SADE[incognita]:=SADE[incognita] union {c||i}
od:
detsyst
end:
# homog_poly_syst
# Returns the homogenized polynomial system by its biggest exponent.
# Synopsis
# result := homog_poly_syst(eqs,vars,nome)
# Parameters
# result: a list of two lists.
# eqs: a list of algebraic expressions.
# vars: a list of variable names.
# nome: a variable name.
# Description
# Returns the homogenized polynomial system by its biggest exponent.
# The first argument is the vector field of the dynamical system, the second one
# the correponding variable names and nome is a name to use as the additional variable in the
# homogeneous system.
# Code
homog_poly_syst:=proc(eqs,vars,nome)
local i,j,prov,prov2,pnf,nd,ndeg,newfield,newvars,numterm,vars2:
ndeg:=0:
vars2:={op(vars)}:
for i from 1 to nops(eqs) do
    prov:=expand(eqs[i]):
    if degree(prov,vars2)>ndeg then
       ndeg:=degree(prov,vars2)
    fi
od:
newfield:=0:
for i from 1 to nops(eqs) do
    prov:=expand(eqs[i]):
    pnf:=0:
    if type(prov,`+`) then
       numterm:=nops(prov)
    else
       numterm:=1
    fi:
    if numterm=1 then
       nd:=degree(prov,vars2):
       pnf:=pnf+prov*nome^(ndeg-nd)
    else
       for j from 1 to numterm do
           prov2:=op(j,prov):
           nd:=degree(prov2,vars2):
           pnf:=pnf+prov2*nome^(ndeg-nd)
       od:
    fi:
    newfield:=newfield,pnf
od:
newvars:=[nome,op(vars)]:
[[newfield],newvars]
end:
# newinv
# Computes invariants from semi-invariants of a general homogeneous system.
# Synopsis
# result := newinv(si)
# Parameters
# result: a list.
# si: a list.
# Description
# Returns a list where the first element is the invariant and the second one
# the conditions on the parameters for the invariant to be valid.
# The input must be a sigle semi-invariant of the output of quasisolve.
# Code
newinv:=proc(si)
local i,j,eq,flow,unk,vars,res,res2,prov,prov2,prov3,sol:
#global walsyst,__nome:
global SADE:
sol:={}:
flow:=subs(si[3],SADE[walsyst][1]):
vars:=SADE[walsyst][2]:
eq:=0:
unk:={}:
for i from 1 to nops(flow) do
    eq:=eq+cat(SADE[_tt],i)*flow[i]:
    unk:=unk union {cat(SADE[_tt],i)}
od:
eq:=eq-si[2]:
unk:=unk union paramcont(eq):
eq:=lifdec2(eq,vars):
res:={solve(eq,unk)}:
if res={} then RETURN({}) fi:
for j from 1 to nops(res) do
    res2:=op(j,res):
    eq:=1:
    for i from 1 to nops(flow) do
        eq:=eq*vars[i]^cat(SADE[_tt],i)
    od:
    eq:=eval(subs(res2,eq)):
    eq:=eval(subs(res2,si[1]))/eq:
    prov3:=paramcont(res2):
    for i from 1 to nops(flow) do
        prov3:=prov3 union {cat(SADE[_tt],i)}
    od:
    prov:=solve(res2,prov3):
    prov2:={}:
    if {prov}<>{} then
       for i from 1 to nops(prov) do
           if paramcont(op(i,prov))<>{} then
              prov2:=prov2 union {op(i,prov)}
           fi
       od
    fi:
    prov:=[eq,si[3] union prov2]:
    sol:=sol union {prov}
od:
sol:=subs(SADE[nome]=1,sol):
simplify(sol)
end:
# newinvariants
# Uses the output of quasisolve to obtain the invariants of the system
# obtained by dividing the semi-invariant by a quasi-monomial with the
# same eigenvalue.
# Synopsis
# result := newinvariants(aa)
# Parameters
# result: a set of lists.
# aa: a set of lists.
# Description
# Uses the output of quasisolve to obtain the invariants of the system
# obtained by dividing the semi-invariant by a quasi-monomial with the
# same eigenvalue.
# Code
newinvariants:=proc(aa)
local i,res:
res:={}:
for i from 1 to nops(aa) do
    res:=res union newinv(op(i,aa))
od:
res
end:
# coeff_hom_syst
# This routine returns the coefficients in a given set of polynomial equations.
# Synopsis
# result := coeff_hom_syst(eqs,nome)
# Parameters
# result: an array.
# eqs: a list with the vector field of the ODE system.
# nome: a variable name to be used as the output.
# Description
# This routine returns the coefficients in a given set of polynomiald equations.
# The results doesn't account for the symmetrization of nome.
# eqs -> must be given in the form of the output of homog_poly_syst,
#               i.e., [vf,vars] where vf is the vector field associated to the dynamical system
#              and vars the corresponding variables in the respective order.
# nome -> is an array to give the coefficients of the monomials in the equations.
# Code
coeff_hom_syst:=proc(eqs,nome)
local i,j,k,dim,vf,vars,numdim,prov,prov2:
vf:=eqs[1]:
vars:=eqs[2]:
dim:=nops(vf):
if vf[1]=0 then
   numdim:=0
else
   numdim:=degree(vf[1],vars)
fi:
if numdim=0 then
   i:=2:
   while numdim=0 and i<=dim do
         numdim:=degree(vf[i],vars):
         i:=i+1
   od:
   if numdim=0 then RETURN(false) fi
fi:
prov:=1..dim:
for i from 1 to numdim do
    prov:=prov, 1..dim
od:
nome:=array(prov):
for i from 1 to dim do
    for j from 1 to dim^numdim do
        prov:=nuplesequence(j,numdim,dim):
        prov2:=1:
        for k from 1 to numdim do
            prov2:=prov2*vars[prov[k]]
        od:
        prov:=op(prov):
        nome[i,prov]:=coeff_hom(vf[i],prov2,vars):
    od
od:
end:
# coeff_hom
# Returns the coefficient of a  monomial of a homogeneous polynomial.
# Synopsis
# result := coeff_hom(a,p,vars)
# Parameters
# result: an algebraic expressions.
# a: an algebraic expression (a monomial).
# p: an algebraic expression (a polynomial).
# vars: a set of variable names.
# Description
# Returns the coefficient of a  monomial (the first argument) of a homogeneous polynomial
# (the second argument) in a set of variables (the third argument).
# Code
coeff_hom:=proc(a,p,vars)
local i,res:
### WARNING: note that `I` is no longer of type `^`
if type(p,`^`) then RETURN(coeff(a,p)) fi:
res:=a:
for i from 1 to nops(p) do
    res:=coeff(res,op(i,p))
od:
res
end:
# verif_if_inv
# Verifies if an ODE system admits a non-polynomial QP-invariant.
# Synopsis
# result := verif_if_inv(vf,vr,parameters)
# Parameters
# result: a set.
# vf: a list of equations.
# vr: a list of variable names.
# parameters: a set with the free parameters in the system.
# Description
#  This routine verifies if the system of equations defined by vf 2(the first argument)
# and the cooresponding variables in vr2 (the list in the second argument) admits a non-polynomial QP-invariant.
# The time variable is specifiec in the third argument and the free parameters are given as a set in the forth argument.
# The output is a set of sets of conditions on the free parameters such that the non-polynomial QP semi-invariant can
# possibly exist.
# Code
verif_if_inv:=proc(vf2,vr2,params)
local i,j,eqs,gh,GMM,dim,numdim,res,th,uv,prov,prov2,etbs,pr,vars,unks,qmon,vf,vr,t:
global SADE:
SADE[parameters]:=params:
vf:=subs(diff=Diff,vf2):
vr:=map(x->op(0,x),vr2):
t:=op(1,vr2[1]):
for i from 1 to nops(vr) do
    vf:=subs(vr2[i]=vr[i],vf)
od:
prov:=eqToCauchy(vf,vr,t):
vf:=prov[1]:
vr:=prov[2]:
algsys(vf,vr,params):
if not(type(SADE[ccount],constant)) then SADE[ccount]:=1 fi:
eqs:=homog_poly_syst(vf,vr,gh):
vars:=[gh,op(vr)]:
coeff_hom_syst(eqs,GMM):
dim:=nops(vars):
numdim:=nops(op(1,[indices(evalm(GMM))]))-1:
etbs:={}:
unks:={}:
qmon:=1:
for i from 1 to dim do
    unks:=unks union {th||i}:
    qmon:=qmon*vars[i]^th||i:
    for j from 1 to dim^numdim do
       prov:=nuplesequence(j,numdim,dim):
       if is_ord(prov) and not(has(i,prov)) then
          prov:=op(prov):
          pr:=th||i*GMM[i,prov]:
          etbs:=etbs union {pr}
       fi:
    od
od:
etbs:={solve(etbs,unks union params)}:
if etbs={} then RETURN({}) fi:
res:={}:
for i from 1 to nops(etbs) do
    #prov:=arrsol({etbs[i]},unks,params):
    prov:=arrange_solution({etbs[i]},unks,params):
    prov2:=op(prov):
    if prov2={} then
       prov2:=subs(gh=1,qmon)
    else
       prov2:=subs({op(prov2),gh=1},qmon)
    fi:
    prov2=subs(th1=0,prov2):
    if setcont(prov2,vars)<>{} then
       #prov:=arrsol({etbs[i]},unks,params):
       prov:=arrange_solution({etbs[i]},unks,params):
       prov2:={}:
       for j from 1 to nops(prov) do
           prov2:=prov2 union {param_only2(prov[j],params)}
       od:
       res:=res union prov2
    fi
od:
res
end:
# is_ord
# Verifies if a list  is ordered in a crescent order.
# Synopsis
# result := is_ord(nuple)
# Parameters
# result: a boolean variable (true or false).
# nulpe: a list.
# Description
# Verifies if the list in the argument of the routine is ordered in a crescent order.
# Code
is_ord:=proc(nuple)
local i,fl:
fl:=true:
for i from 1 to nops(nuple)-1 do
    if nuple[i]>nuple[i+1] then
       fl:=false
    fi
od:
fl
end:
# diag_lin
# Diagonalizes the linear part of a dynamical system.
# Synopsis
# result := diag_lin(fld,vars,vv)
# Parameters
# result: a list.
# fld: a list.
# vars: a list:
# vv: a variable name.
# Description
# This routine diagonalizes the linear part of the dynamical system
# defined by the vector field fld (first argument) and the respective variables in vars (second argument).
# The name in vv (the third argument) will be used for the new variables as vv1, vv2, ...
# Code
diag_lin:=proc(fld,vars,vv)
local i,j,bb,ss,tt,dim,eigv,rule,res,newvars,prov:
dim:=nops(vars):
bb:=array(1..dim,1..dim):
rule:={}:
for i from 1 to dim do
    rule:=rule union {vars[i]=0}
od:
for i from 1 to dim do
    prov:=expand(fld[i]):
    for j from 1 to dim do
        bb[i,j]:=subs(rule,coeff(prov,vars[j]))
    od
od:
eigv:=[eigenvects(bb)]:
newvars:=vv||1:
for i from 2 to dim do
    newvars:=newvars,vv||i
od:
newvars:=[newvars]:
prov:={}:
for i from 1 to nops(eigv) do
    prov:=prov union eigv[i][3]
od:
eigv:=convert(prov,list):
ss:=array(1..dim,1..dim):
for i from 1 to dim do
for j from 1 to dim do
    ss[j,i]:=eigv[i][j]
od
od:
tt:=linalg[inverse](ss):
rule:={}:
for i from 1 to dim do
    prov:=0:
    for j from 1 to dim do
        prov:=prov+ss[i,j]*vv||j
    od:
    rule:=rule union {vars[i]=prov}
od:
for i from 1 to dim do
    prov:=0:
    for j from 1 to dim do
        prov:=prov+tt[i,j]*fld[j]
    od:
    if i=1 then
       res:=prov
    else
       res:=res,prov
    fi
od:
res:=subs(rule,[res]):
rule:=solve(rule,{op(newvars)}):
res:=[simplify(res),newvars,rule]:
res
end:
# tautoelim
# This routine eliminates tautologies from a set of boolean conditions or a set of sets
# of boolean conditions.
# Synopsis
# result := tautoelim(eqs)
# Parameters
# result: a set.
# eqs: a set.
# Description
# This routine eliminates tautologies from a set of boolean conditions or a set of sets
# of boolean conditions (the argument of the routine).
# Code
tautoelim:=proc(eqs)
local i,res:
if nargs=0 then RETURN({}) fi:
if eqs={} then RETURN(eqs) fi:
res:={}:
if type(eqs[1],set) then
   for i from 1 to nops(eqs) do
       res:=res union {tautoelim(eqs[i])}
   od:
   RETURN(res)
fi:
for i from 1 to nops(eqs) do
    if op(1,eqs[i])<>op(2,eqs[i]) then
       res:=res union {eqs[i]}
    fi
od:
res
end:
# arrange_solution
# This routine puts the solution in the form to be used by QPSI.
# Synopsis
# result := arrange_solution(a,unknowns,parameters)
# Parameters
# result: a set of sets of boolean conditions.
# a: a set of sets of boolean conditions.
# unknowns: a set of variable names (the unkowns of the original problem).
# parameters: a set of variables names (the free parameters in the problem).
# Description
# This routine puts the solution of quasisolve (the first argument) in the form to be used by QPSI.
# The free parameters are given in a set to be given as the third argument.
# Code
arrange_solution:=proc(s,inc,par)
local i,j,eqs,eqs2,cf,sol,prov,prov2,p,res:
sol:=tautoelim(s):
if nops(sol)>0 and type(sol[1],set) then
   res:={}:
   for i from 1 to nops(sol) do
       res:=res union arrange_solution(sol[i],inc,par):
   od:
   RETURN(res)
fi:
eqs:={}:
eqs2:={}:
cf:=setcont(sol,inc minus par):
for i from 1 to nops(sol) do
    if has(sol[i],cf) then
       eqs:=eqs union {sol[i]}
    else
       eqs2:=eqs2 union {sol[i]}
    fi
od:
if eqs<>{} then
   res:={}:
   prov:=eqs[1]:
   eqs:=eqs minus {prov}:
   if has(op(1,prov),cf) then
      p:={{prov}}
   else
      p:=simplify({solve(prov,setcont(prov,cf))})
   fi:
   for i from 1 to nops(p) do
       prov:=simplify(subs(p[i],eqs)):
       prov:=arrange_solution(prov,inc,par):
       for j from 1 to nops(prov) do
           prov2:=subs(prov[j],p[i]) union prov[j] union eqs2:
           res:=res union {prov2}
       od
   od
else
   res:={eqs2}
fi:
res:=tautoelim(res):
res    
end:
# arrsol
# Transforms an output of solve into an usable and presentable form.
# Synopsis
# result := arrsol(sol,parameters)
# Parameters
# result:  a set of sets of boolean conditions.
# sol: a set of sets of boolean conditions.
# parameters: a set of variable names.
# Description
# This routine transforms the expression sol (the first argument), which is an output of solve, into an usable
# and presentable form with respect to parameters (the second argument).
# Code
arrsol:=proc(sol,unknowns,parameters)
local res,eqs,var:
res:={}:
var:=setcont(sol,parameters):
eqs:=sol:
res:=arrange_solution(eqs,unknowns,parameters):
res
end:
# param_only
# This routine keeps from a set of boolean conditions those involving  the _ci and _Ci coefficients.
# Synopsis
# result := param_only(a,parameters)
# Parameters
# result: a set.
# a: a set.
# parameters: a set of variable names.
# Description
# This routine keeps from a set of boolean conditions (the first argument) those involving
# the  _ci and _Ci coefficients(the second argument).
# Code
param_only:=proc(a,parameters)
local i,res:
res:={}:
for i from 1 to nops(a) do
    if ccont2(a[i])={} then
       res:=res union {a[i]}
    fi
od:
res
end:
# param_only2
# This routine keeps from a set of boolean conditions those involving  the free  parameters.
# Synopsis
# result := param_only2(a,parameters)
# Parameters
# result: a set.
# a: a set.
# parameters: a set of variable names.
# Description
# This routine keeps from a set of boolean conditions (the first argument) those involving
# the free  parameters (the second argument).
# Code
param_only2:=proc(a,parameters)
local i,res:
res:={}:
for i from 1 to nops(a) do
    if has(op(1,a[i]),parameters) then
       res:=res union {a[i]}
    fi
od:
res
end:
# ccont2
# Returns the set of variables cat(SADE[_tt],i) in the argument.
# Synopsis
# result := ccont2(a)
# Parameters
# result: a set.
# a: any maple expression.
# Description
# Returns the set of variables cat(SADE[_tt],i) in the argument.
# Code
ccont2:=proc(a)
local i,res:
global SADE:
res:=ccont(a) union C_Ccont(a):
for i from 1 to SADE[dim] do
    if has(a,cat(SADE[_tt],i)) then
       res:=res union {cat(SADE[_tt],i)}
    fi
od:
res
end:
# keep_not_c
# Returns the elements of a set not containing any variable cat(SADE[_tt],i).
# Synopsis
# result := keep_not_c(a)
# Parameters
# result: a set.
# a: a set.
# Description
# Returns the elements of a set not containing any variable cat(SADE[_tt],i).
# Code
keep_not_c:=proc(a)
local i,res,pr:
res:={}:
for i from 1 to nops(a) do
    pr:=a[i]:
    if ccont2(pr)={} then
       res:=res union {pr}
    fi
od:
res
end:
# c_solve
# Solves a set of boolean conditions in the constants __c.i puting any parameter
# dependence on the right hand side.
# Synopsis
# result := c_solve(eq,var)
# Parameters
# result: a set of boolean conditions.
# eq: a set of boolean conditions.
# var: a set of variable names
# Description
# Solves a set of boolean conditions (the first argument)  in the constants __c.i puting any parameter
# dependence on the right hand side.
# Code
c_solve:=proc(eq)
local i,j,res,eqs,sol,prov,prov2:
global SADE:
prov:=arrsol({eq},SADE[incognitas],SADE[parameters]):
res:={}:
for i from 1 to nops(prov) do
    prov2:=subs(prov[i],eq):
    eqs:={solve(prov2,ccont(prov2))}:
    for j from 1 to nops(eqs) do
        res:=res union tautoelim({eqs[j]})
    od
od:
res
end:
# coordtr
# Transforms the tensor TT, of kind (n,m) from the quasi-monomial variables into the original variables.
# Synopsis
# result := coordtr(TT,n,m)
# Parameters
# result: an array.
# TT: an array.
# n,m: integers.
# Description
# Transforms the tensor TT (the first argumet), of kind (n,m) (the second and third arguments
# respectively)from the quasi-monomial variables into the original variables.
# Code
coordtr:=proc(TT,n,m)
local i,j,k,nbmat,nbmatinv,varr,nn,mm,lambda,lambdabar,UU,dim,prov,prov2,ind,ind2:
#global __field,qmlist,matb:
global SADE:
varr:=op(SADE[field][2]):
mm:=nops(SADE[qmlist]):
nn:=nops([varr]):
for i from nn+1 to mm do
    varr:=varr,1
od:
varr:=[varr]:
dim:=1..mm:
for i from 2 to n+m do
    dim:=dim,1..mm
od:
UU:=array(dim):
nbmat:=array(1..mm,1..mm):
for i from 1 to nn do
    for j from 1 to mm do
        nbmat[j,i]:=SADE[QMatB][j,i]
    od
od:
for i from nn+1 to mm do
    for j from 1 to mm do
# Here I changed = by <>.
        if i<>j then
           nbmat[j,i]:=1
        else
           nbmat[j,i]:=0
        fi
    od
od:
nbmatinv:=linalg[inverse](nbmat):
lambda:=array(1..mm,1..mm):
lambdabar:=array(1..mm,1..mm):
for i from 1 to mm do
for j from 1 to mm do
      prov:=nbmatinv[j,i]*varr[j]:
      prov2:=nbmat[i,j]/varr[j]:
      for k from 1 to mm do
          prov:=prov*varr[k]^(-nbmat[i,k]):
          prov2:=prov2*varr[k]^nbmat[i,k]
      od:
      lambda[i,j]:=prov:
      lambdabar[i,j]:=prov2
od
od:
for i from 1 to mm^(n+m) do
    ind:=op(nuplesequence(i,n+m,mm)):
    prov:=0:
    for j from 1 to mm^(n+m) do
        ind2:=op(nuplesequence(j,n+m,mm)):
        prov2:=TT[ind2]:
        for k from 1 to n do
            prov2:=prov2*lambda[op(k,[ind2]),op(k,[ind])]
        od:
        for k from 1 to m do
            prov2:=prov2*lambdabar[op(k+n,[ind2]),op(k+n,[ind])]
        od:
        prov:=prov+prov2
    od:
    UU[ind]:=final_form(prov)
#    UU[ind]:=prov
od:
UU
end:
# matreorg
#  Rearranges the matrices mata,matb,matm and the list qmlist so that the extended B matrix is inversible.
# Synopsis
# result := matreorg()
# Parameters
# result: null
# Description
# Rearranges the matrices mata,matb,matm and the list qmlist so that the extended B matrix is inversible.
# Code
matreorg:=proc()
local i,j,prov,prov2,nn,mm,res,qm:
#global mata,matb,matm,qmlist:
global SADE:
nn:=nops(SADE[qmlist]):
mm:=linalg[coldim](SADE[QMatB]):
for i from 1 to nn do
    if SADE[qmlist][i]=1 then
       prov:=evalm(SADE[QMatB][nn,1]):
       prov2:=evalm(SADE[QMatA][1,nn]):
       for j from 2 to mm do
           prov:=prov,evalm(SADE[QMatB][nn,j]):
           prov2:=prov2,evalm(SADE[QMatA][j,nn])
       od:
       prov:=[prov]:
       prov2:=[prov2]:
       for j from 1 to mm do
           SADE[QMatB][nn,j]:=evalm(SADE[QMatB][i,j]):
           SADE[QMatA][j,nn]:=evalm(SADE[QMatA][j,i]):
       od:
       for j from 1 to mm do
           SADE[QMatB][i,j]:=prov[j]:
           SADE[QMatA][j,i]:=prov2[j]
       od:
       res:=cat(SADE[__U],1):
       for j from 2 to nn do
           res:=res,cat(SADE[__U],j)
       od:
       res:=[res]:
       res:=subs(cat(SADE[__U],i)=qm,res):
       res:=subs(cat(SADE[__U],nn)=cat(SADE[__U],i),res):
       res:=subs(qm=cat(SADE[__U],nn),res):
       res:=final_form(res):
       SADE[qmlist]:=res:
       SADE[matm]:=matrix_prod(SADE[QMatB],SADE[QMatA]):
       SADE[dim]:=linalg[rowdim](SADE[matm]):
       RETURN()
    fi
od:
end:
# geom_meth_inv
# Obtains all possible invariants from the symmetries (or forms) obtained from the output of quasisolve.
# Synopsis
# result := geom_meth_inv(aa)

# Parameters
# result: a set of lists.
# Description
# Obtains all possible invariants from the symmetries (or forms) obtained from the output of quasisolve
# (the first argument).
# Code
geom_meth_inv:=proc(aa)
local i,j,argm,pr,res,nn,gseq,prov,dim:
global SADE:
if aa={} then RETURN({}) fi:
if nops(aa[1])>2 then RETURN({}) fi:
dim:=nops(aa[1][1]):
res:=ld_meth_inv(aa):
if nops(aa)<dim then RETURN(res) fi:
if setcont(aa,SADE[field][2])={} then
   pr:=final_form(aa,0)
else
   pr:=aa
fi:
if pr={} then RETURN({}) fi:
nn:=nops(pr):
res:={}:
prov:=permute(nn,dim):
gseq:={}:
for i from 1 to nops(prov) do
    gseq:=gseq union {{op(op(i,prov))}}
od:
for i from 1 to nops(gseq) do
    argm:=pr[op(1,op(i,gseq))]:
    for j from 2 to dim do
        argm:=argm,pr[op(j,op(i,gseq))]
    od:
    prov:=geom_meth_aux(argm):
    if setcont(prov,SADE[field][2])<>{} then
       res:=res union prov
    fi
od:
res
end:
# geom_meth_aux
# Computes the invariants associated to a set of generators using the geometrical nethod.
# Synopsis
# result := geom_meth_aux()
# Parameters
# result: a set of lists.
# args: lists.
# Description
# Computes the invariants associated to a set of generators (the inputs of the reoutine)
# using the geometrical nethod.
# Code
geom_meth_aux:=proc()
local cond,dim,i,j,k,prov,prov2,prov3,res,mat,inv,teste,fflv:
#global __field,parameters,__lvfield:
global SADE:
dim:=nargs:
prov2:=args[1][2]:
prov:=convert(args[1][1],list):
for i from 2 to nargs do
    prov:=prov,convert(args[i][1],list):
    prov2:=prov2 union args[i][2]
od:
cond:={solve(prov2,SADE[parameters])}:
if cond={} then RETURN({}) fi:
if nops(cond)>1 then
   inv:={}:
   for i from 1 to nops(cond) do
       prov:=subs(cond[i],[args[1..nargs]]):
       prov:=op(prov):
       inv:=inv union geom_aux(prov)
   od:
   RETURN(inv)
fi:
cond:=cond[1]:
prov:=subs(cond,[prov]):
mat:=array(prov):
teste:=det(mat):
teste:=traperror(simplify(teste)):
if teste<>0 and teste<>lasterror then
   if SADE[nind]<>1 and SADE[mind]<>0 then
      RETURN({})
   fi:
   fflv:=final_form(SADE[lvfield][1]):
   prov:=array(prov):
   prov:=linalg[inverse](prov):
   res:={}:
   for i from 1 to dim do
       prov2:=0:
       for j from 1 to dim do
           prov2:=prov2+prov[j,i]*fflv[j]
       od:
       res:=res union {[prov2,cond]}
   od:
   RETURN(res)
fi:
inv:={}:
prov2:={}:
for i from 1 to dim do
    prov:=0:
    prov2:=prov2 union {cat(SADE[_c],i)}:
    for j from 1 to dim do
        prov:=prov+mat[j,i]*cat(SADE[_c],j)
    od:
    inv:=inv union {prov}
od:
prov:={solve(inv,prov2)}:
inv:={}:
for i from 1 to nops(prov) do
    inv:=inv union subs(prov[i],prov2):
od:
inv:=inv minus prov2:
res:={}:
for i from 1 to nops(inv) do
    prov:=inv[i]:
    if setcont(prov,SADE[field][2])<>{} then
       teste:=setcont(prov,prov2):
       for j from 1 to nops(teste) do
           prov3:=prov:
           for k from 1 to nops(teste) do
               if j=k then
                  prov3:=subs(teste[j]=1,prov3)
               else
                  prov3:=subs(teste[j]=0,prov3)
               fi
           od:
           res:=res union {[prov3,cond]}
       od
    fi
od:
res
end:
# ld_meth_inv
# Computes the invariants associted to symmetries such that two generators are linearly dependent.
# Synopsis
# result := ld_meth_inv:=proc(aa)
# Parameters
# result: a set of lists.
# aa: a set os lists.
# Description
# Computes the invariants associted to symmetries (the set in the input)
# such that two generators are linearly dependent.
# Code
ld_meth_inv:=proc(aa)
local i,j,nn,res,a,b,pr:
global SADE:
nn:=nops(aa):
res:={}:
for i from 1 to nn-1 do
for j from i+1 to nn do
    a:=aa[i]:
    b:=aa[j]:
    pr:=ld_meth_aux(a,b):
    if setcont(pr,SADE[field][2])<>{} then
       res:=res union pr
    fi
od
od:
res
end:
# ld_meth_aux
# Returns the invariant associated to a given pair of generators.
# Synopsis
# result := ld_meth_aux(a,b)
# Parameters
# result: a set with a list.
# Description
# Returns the invariant associated to a given pair of generators (the first and second arguments).
# Code
ld_meth_aux:=proc(a,b)
local i,j,nn,prov1,prov2,tf,res,cond,aa,bb:
global SADE:
aa:=[convert(a[1],list),a[2]]:
bb:=[convert(b[1],list),b[2]]:
nn:=nops(aa[1]):
if nn=1 then RETURN({}) fi:
for i from 1 to nn do
    if op(i,aa[1])=0 and op(i,bb[1])<>0 then RETURN({}) fi:
    if op(i,aa[1])<>0 and op(i,bb[1])=0 then RETURN({}) fi
od:
cond:=aa[2] union bb[2]:
cond:={solve(cond,SADE[parameters])}:
if cond={} then RETURN({}) fi:
if nops(cond)>1 then
   res:={}:
   for i from 1 to nops(cond) do
       prov1:=subs(cond[i],aa[1]):
       prov2:=subs(cond[i],bb[1]):
       res:=res union ld_meth_aux([prov1,cond[i]],[prov2,cond[i]])
   od:
   RETURN(res)
fi:
cond:=cond[1]:
j:=1:
while op(j,bb[1])=0 do
      j:=j+1:
      if j>nn then RETURN(0) fi
od:
prov1:=simplify(op(j,aa[1])/op(j,bb[1])):
tf:=true:
for i from j+1 to nn do
    if op(i,bb[1])<>0 then
       prov2:=simplify(op(i,aa[1])/op(i,bb[1])):
       if prov1<>prov2 then tf:=false fi
    fi
od:
if tf then
      res:=prov1
else
      res:=0
fi:
prov2:={}:
for i from 1 to nops(cond) do
    if op(1,cond[i])<>op(2,cond[i]) then
       prov2:=prov2 union {cond[i]}
    fi
od:
{[res,prov2]}
end:
# rat_meth_aux
# Looks for a rational invariant assotiated to two semi-invariants format of the output of quasisolve.
# Synopsis
# result := rat_meth_aux(a,b,t)
# Parameters
# result: a set of lists.
# a: a list (a semi-invariant).
# b: a list (a semi-invariant).
# t: a variables name (the time variable).
# Description
# This routine looks for a rational invariant assotiated to two semi-invariants
# (the first two arguments) in the format of the output of quasisolve.
# The third argument is the variable used as the time parameter in the invariants in the output.
# Code
rat_meth_aux:=proc(a,b,t)
local i,j,m,a2,b2,ps1,ps2,lmb1,lmb2,cond,cond2,unk,unk2,prov,p,res,qm,qm2,qmt,
      eq,_tht,sigma,inv,cont,pot,p2,p3:
global SADE:
m:=nops(SADE[qmlist]):
a2:=final_form(a):
b2:=final_form(b):
ps1:=a2[1]:
ps2:=b2[1]:
lmb1:=a2[2]:
lmb2:=b2[2]:
cond:=a[3] union b[3]:
unk:={}:
for i from 1 to nops(cond) do
    unk:=unk union {op(1,cond[i])}
od:
prov:=solve(cond,unk):
if {prov}={} or prov={} then
   RETURN({})
fi:
prov:=arrange_solution({prov},SADE[incognita],SADE[paramaters]):
#prov:=param_only(prov):
if nops(prov)>1 then
   res:={}:
   for i from 1 to nops(prov) do
       p:=prov[i]:
       p2:=traperror([subs(p,ps1),subs(p,lmb1),p]):
       p3:=traperror([subs(p,ps2),subs(p,lmb2),p]):
       if p2<>lasterror and p3<>lasterror then
          res:=res union rat_meth_aux([subs(p,ps1),subs(p,lmb1),p],
                                      [subs(p,ps2),subs(p,lmb2),p],t)
       fi
   od:
   RETURN(res)
fi:
p:=prov[1]:
ps1:=traperror(subs(p,ps1)):
if ps1=lasterror then RETURN({}) fi:
ps2:=traperror(subs(p,ps2)):
if ps2=lasterror then RETURN({}) fi:
lmb1:=traperror(subs(p,lmb1)):
if lmb1=lasterror then RETURN({}) fi:
lmb2:=traperror(subs(p,lmb2)):
if lmb2=lasterror then RETURN({}) fi:
qm:=1:
qmt:=0:
unk:=setcont(p,SADE[parameters]):
for i from 1 to m do
    qm:=qm*cat(SADE[__U],i)^cat(_tht,i):
    for j from 1 to m do
        qmt:=qmt+cat(_tht,i)*SADE[matm][i,j]*cat(SADE[__U],j):
        unk:=unk union {cat(_tht,i)}
    od
od:
qmt:=subs(p,final_form(qmt)):
qm:=subs(p,final_form(qm)):
res:={}:
for pot from -1 to 1 by 2 do
    if has(SADE[qmlist],1) then
       eq:=lmb1+pot*lmb2+qmt+sigma:
       unk:=unk union setcont(eq,SADE[parameters]) union {sigma}
    else
       eq:=lmb1+pot*lmb2+qmt:
       unk:=unk union setcont(eq,SADE[parameters]):
       sigma:=0
    fi:
    unk2:=unk minus SADE[parameters]:#print(111,eq):
    eq:=lifdec2(eq,SADE[field][2]):#print(222,eq):
    prov:={solve(eq,unk)}:
    prov:=arrange_solution(prov,unk,SADE[parameters]):#print(333,pot,prov):
    if prov={{}} then prov:={} fi:
    for i from 1 to nops(prov) do
        cond:=traperror(subs(prov[i],p)):
        if cond<>lasterror then
           inv:=traperror(subs(prov[i],ps1*ps2^pot*qm*exp(sigma*t))):
           if inv<>lasterror then
              cond2:=p:
              for j from 1 to nops(prov[i]) do
                  if not(has(prov[i][j],unk2)) then
                     cond2:=cond2 union {prov[i][j]}
                  fi
              od:
              if cond2<>{} then
                 cond2:=solve(cond2,setcont(cond2,SADE[parameters])):
                 if {cond2}={} then cond2:=false fi
              fi:
              if cond2<>false then
                 cont:=0:
                 for j from 1 to m do
                     if has(inv,cat(_tht,j)) then
                        cont:=cont+1:
                        inv:=subs(cat(_tht,j)=cat(SADE[_tt],cont),inv)
                     fi
                 od:
                 res:=res union {[eval(inv),tautoelim(cond2)]}
              fi
           fi
        fi
    od
od:
res
end:
# solinvert
# Inverts a solution with respect a set of variables.
# Synopsis
# result := solinvert(sl,tts)
# Parameters
# result: a setof boolena conditions.
# sl: a set of boolean conditions.
# tts: a set of variable names.
# Description
# Inverts a solution (the first argument) with respect a set of variables (the second argument).
# Code
solinvert:=proc(sl,tts)
local i,j,res,prov,prov2,vv,sol:
if sl={} then RETURN({}) fi:
if not(type(sl,set)) then
   RETURN(sl)
fi:
if type(s1[1],set) then
   res:={}:
   for i from 1 to nops(sol) do
       res:=res union {solinvert(sol[i],tts)}
   od:
   RETURN(res)
fi:
sol:={}:
for i from 1 to nops(sl) do
    if op(1,sl[i])<>op(2,sl[i]) then
       sol:=sol union {sl[i]}
    fi
od:
res:={}:
sol:=[op(sol)]:
for i from 1 to nops(sol) do
    prov:=sol[i]:
    vv:=setcont(op(2,prov),tts):
    if setcont(op(1,prov),tts)={} and vv<>{} then
       prov2:=solve(prov,{vv[1]}):
       if nops({prov2})>1 then
          prov2:={prov2}:
          prov:={}:
          for j from 1 to nops(prov2) do
              prov:=prov union {res union solinvert(subs(prov2[j],{op(sol)}),tts)}
          od:
          RETURN(prov)
       fi:
       sol:=subs(prov2,sol):
       res:=res union prov2
    else
       res:=res union {prov}
    fi
od:
res:=[op(res)]:
for i from 1 to nops(res) do
    prov:=res[i]:
    if i=1 then
       prov2:=prov:
       for j from 2 to nops(res) do
           prov2:=prov2,subs(prov,res[j])
       od:
       res:=[prov2]
    else
       prov2:=res[1]:
       for j from 2 to nops(res) do
           if i=j then
              prov2:=prov2,prov
           else
              prov2:=prov2,subs(prov,res[j])
           fi
       od:
       res:=[prov2]
    fi
od:
res
end:
# invariant
# Returns all quasipolinomial rational invariants from the output of quasisolve.
# Synopsis
# result := invariant(a,t)
# Parameters
# result: a set of lists (the output of quasisolve or a subset of it)..
# t: a variable name (teh time variable).
# Description
# Returns all quasipolinomial rational invariants from the output of quasisolve (the first argument).
# Code
invariant:=proc(a,t)
local i,j,b,res:
b:=a union {[1,0,{}]}:
res:={}:
for i from 1 to nops(a)-1 do
for j from i+1 to nops(a) do
    res:=res union rat_meth_aux(b[i],b[j],t)
od
od:
res
end:
# tau_solve
# Solves for the tau dependence in the routine invariants..
# Synopsis
# result := tau_solve(a)
# Parameters
# result: a list.
# a: a list.
# Description
# Solves for the tau dependence in the routine invariants.
# Code
tau_solve:=proc(a)
local inv,cond,prov,prov2,res,i,j:
global ___tempo:
inv:=a[1]:
cond:=a[2]:
if not(has(cond,___tempo)) then RETURN(a) fi:
for i from 1 to nops(cond) do
    prov2:=cond[i]:
    if op(1,prov2)<>SADE[tau] and has(prov2,___tempo) then
       res:={}:
       prov:={solve(prov2,setcont(prov2,___tempo))}:
       for j from 1 to nops(prov) do
           res:=res union {subs(prov[j],[inv,cond minus {prov2}])}
       od:
       RETURN(op(res))
    fi
od:
a
end:
# polyn_cmpt
# Returns a polynomial in a set of variables of a given order.
# Synopsis
# result := polyn_cmpt(order,vard)
# Parameters
# result: an algebraic expression.
# order: an integer.
# vard: a set of variable names.
# Description
# Returns a polynomial of a given order (the first argument) in variables vard (the second arhument).
# Code
polyn_cmpt:=proc(order,vard)
local i1,i2,prov,prov2,flag:
global SADE:
prov:=1:
for i1 from 1 to nops(vard) do
     prov2:=1:
     for i2 from 1 to order do
          prov2:=prov2+op(i1,vard)^i2
     od:
     prov:=prov*prov2
od:
prov:=expand(prov):
prov2:=0;
for i1 from 1 to nops(prov) do
     if degree(op(i1,prov),vard)<=order then
        prov2:=prov2+cat(SADE[_c],SADE[ccount])*op(i1,prov):
        SADE[ccount]:=SADE[ccount]+1:
     fi
od:
prov2
end:
# constlog
#
# Computes polynomial-logarithmic constants of motion using the routines poly_inv_log
# and polylog_inv. The first argument is the set of equations, the second the set of unknowns
# in the equations. If the equations are in the Diff format, the next argument is the time
# variable. The next arguments are the set of free parameters in the equations and the order
# of the polynomials in the constants of motion. A last optional argument as Groebner
# first computer the Groebner basis for the determining system to be solved.
#
constlog:=proc()
local i,eqs,dep,time,params,prov,n,r,p:
eqs:=args[1]:
dep:=[op(args[2])]:
if type(dep[1],function) then
   prov:=map(x->op(0,x),dep):
   time:=op(1,dep[1]):
   eqs:=convert(eqs,Diff):
   for i from 1 to nops(dep) do
       eqs:=subs(dep[i]=prov[i],eqs)
   od:
   dep:=prov:
   params:=args[3]:
   n:=args[4]
else
   time:=args[3]:
   params:=args[4]:
   n:=args[5]
fi:
LVformat(eqs,dep,time,params):
if has({args},Groebner) then
   r:=poly_inv_log(n,1):
   r:=r union polylog_inv(n,1)
else
   r:=poly_inv_log(n):
   r:=r union polylog_inv(n)
fi:
i:=1:
p:={}:
while has(r,cat(_tt,i)) do
      p:=p union {cat(_tt,i)}:
      i:=i+1
od:
for i from 1 to nops(p) do
    r:=subs(p[i]=cat(_C,i),r)
od:
r
end:
# poly_inv_log
#
# Computes invariants of the form: polynom+constant*log(quasi-monome),
# where n is the order of the polynomial. If a second argument is given
# (no matter its value) then the determinant system is solved using grobner basis 
#
poly_inv_log:=proc(n)
local prov,prov2,i,j,vv,dim,th,eq,monom,pol,cond,res:
#global matm,ccount,__psi,__lambda,unknowns,parameters,vars:
global SADE:
SADE[ccount]:=1:
dim:=linalg[rowdim](SADE[matm]):
vv:=cat(SADE[__U],1):
for i from 1 to dim do
    vv:=vv,cat(SADE[__U],i)
od:
vv:=[vv]:
prov:=polyn_cmpt(n,vv):
SADE[__psi]:=prov:
SADE[__lambda]:=0:
SADE[incognita]:=SADE[parameters]:
for i from 1 to SADE[ccount]-1 do
    SADE[incognita]:=SADE[incognita] union {cat(SADE[_c],i)}
od:
for i from 1 to dim do
    th[i]:=cat(SADE[_c],SADE[ccount]):
    SADE[incognita]:=SADE[incognita] union {th[i]}:
    for j from 1 to dim do
        SADE[__lambda]:=SADE[__lambda]+cat(SADE[_c],SADE[ccount])*SADE[matm][i,j]*cat(SADE[__U],j)
    od:
    SADE[ccount]:=SADE[ccount]+1
od:
eq:=0:
for i from 1 to dim do
for j from 1 to dim do
    eq:=eq+diff(prov,cat(SADE[__U],i))*cat(SADE[__U],i)*SADE[matm][i,j]*cat(SADE[__U],j)
od
od:
eq:=eq+SADE[__lambda]:
monom:=1:
for i from 1 to dim do
    monom:=monom*cat(SADE[__U],i)^th[i]
od:
SADE[__lambda]:=[SADE[__lambda],monom]:
eq:=final_form(eq):
eq:=lifdec2(eq,SADE[_vars]):
if nargs>1 then
   eq:=quasisolve(eq,0)
else
   eq:=quasisolve(eq)
fi:
eq:=eq minus {[1,0,{}]}:
res:={}:
for i from 1 to nops(eq) do
    pol:=eq[i][1]:
    cond:=eq[i][3]:
    prov2:=eq[i][2][2]:
    prov:=pol+log(prov2):
    prov:=final_form(prov):
    if setcont(prov,SADE[_vars])<>{} and not(type(prov,numeric)) then
       prov2:=C_Ccont(prov):
       for j from 1 to nops(prov2) do
           prov:=subs(prov2[j]=cat(SADE[_tt],j),prov)
       od:
       res:=res union {[prov,cond]}
    fi
od:
res minus {[1,{}]}
end:
# polylog_inv
#
# This routine computes invariants of the form P(U,ln(U)), where P(x,y) is a polynomial of
# order n in x and y. If a second argument is given (any) then the routine uses
# Grobner basis (gsolve) to solve the algebraic determining system
#
polylog_inv:=proc(n)
local var1,var2,UL,dim,prov,i,j,eq,res,oldvar:
#global matm,__psi,__lambda,ccount,unknowns,parameters,vars:
global SADE:
oldvar:=SADE[_vars]:
SADE[_vars]:=SADE[field][2]:
dim:=linalg[rowdim](SADE[matm]):
var1:=cat(SADE[__U],1):
var2:=UL1:
for i from 2 to dim do
    var1:=var1,cat(SADE[__U],i):
    var2:=var2,UL||i
od:
prov:=polyn_cmpt(n,[var1,var2]):
for i from 1 to dim do
    prov:=subs(UL||i=ln(cat(SADE[__U],i)),prov)
od:
SADE[__psi]:=prov:
SADE[__lambda]:=0:
eq:=0:
for i from 1 to dim do
for j from 1 to dim do
    eq:=eq+diff(prov,cat(SADE[__U],i))*U||i*SADE[matm][i,j]*cat(SADE[__U],j)
od
od:
SADE[incognita]:={}:
for i from 1 to SADE[ccount]-1 do
    SADE[incognita]:=SADE[incognita] union {cat(SADE[_c],i)}
od:
SADE[incognita]:=SADE[incognita] union SADE[parameters]:
eq:=normal(eq):
eq:=numer(eq):
eq:=final_form(eq):
eq:=lifdec2(eq,SADE[_vars]):
if nargs>1 then
   eq:=quasisolve(eq,0)
else
   eq:=quasisolve(eq)
fi:
eq:=eq minus {[1,0,{}]}:
eq:=final_form(eq):
res:={}:
for i from 1 to nops(eq) do
    if setcont(eq[i],SADE[_vars])<>0 then
       prov:=[eq[i][1],eq[i][3]]:
       res:=res union {prov}
    fi
od:
SADE[_vars]:=oldvar:
res
end:
# lifdec2
# Returns when possible the set of the coefficients in the expression in a set of variables.
# Synopsis
# result := lifdec2(a,y)
# Parameters
# result: a set of expressions.
# a: an expressions.
# y: a variable name.
# Description
# Returns when possible the set of the coefficients in the expression a (the first argument)
# of the expansion of all lineraly independent funcions of the variables  in y (the second arument).
# Code
lifdec2:=proc(a,y)
local ghost,prov,fnclist,res,i:
fnclist:=lifunc2(a,y):
if fnclist={} then
   RETURN({a})
fi:
prov:=rpsub2(op(1,fnclist),ghost,a):
prov:={coeffs(prov,ghost)}:
res:={}:
for i from 1 to nops(prov) do
    res:=res union lifdec2(prov[i],y)
od:
res
end:
# lifunc2
# Returns the set of lineraly independent functions on a set of variables found in an expression.
# Synopsis
# result := lifunc2(a,y)
# Parameters
# result: a set of expressions.
# a: an algebraic expression.
# y: a set of variable names.
# Description
#  Returns the set of lineraly independent functions of the variables in y (the second argument)
#  found in the expression a (the first argument).
# Code
lifunc2:=proc(a,y)
local i,j,prov,prov2,ghost,res:
prov:=a:
if not(type(prov,`+`)) then prov:=prov+ghost fi:
res:={}:
for i from 1 to nops(prov) do
        prov2:=op(i,prov):
        if has(prov2,y) then
                if type(prov2,`*`) then
                        for j from 1 to nops(prov2) do
                                if has(op(j,prov2),y) then
                                        res:=res union {op(j,prov2)}
                                fi
                        od
                else
                        res:=res union {prov2}
                fi
        fi
od:
res
end:
# rpsub
#
# Replaces a by b in c, provided that a occurs lienarly in c. It is not required that
# a is an operand of c.
#
rpsub:=proc(a,b,c)
local i,res,p1,p2,_gh,inv,a2,flag:
############################
if type(c,`+`) then
   RETURN(map(x->rpsub(a,b,x),c))
fi:
############################
if type(a,`*`) then
   p1:={}:
   p2:=1:
   inv:={}:
   res:=c:
   a2:=orderfunctions({op(a)}):
   for i from 1 to nops(a2) do
       res:=subs(op(i,a2)=cat(_gh,i),res):
       p1:=p1 union {cat(_gh,i)}:
       p2:=p2*cat(_gh,i):
       inv:=inv union {cat(_gh,i)=op(i,a2)}
   od:
   i:=1:
   flag:=true:
   while i<=nops(a2) and flag do
         res:=traperror(coeff(res,p1[i])):
         if res=lasterror then flag:=false fi:
         i:=i+1
   od:
   if flag then
      res:=expand(subs(inv,c-res*p2)+res*b)
   fi
else
   flag:=true:
   res:=subs(a=b,c)
fi:
if not(flag) then
   res:=c
fi:
res
end:
# rpsub2
# Replacement of a variable provided it is not an argument of a function, including exponents.
# Synopsis
# result := rpsub2(a,b,arg)
# Parameters
# result: an algebraic expression.
# a: a variable name.
# b: a variable name.
# arg: an expressions
# Description
#  Replaces a (1-st argument) by b (2-nd argument)  in the expression arg (3-rd argument)
#  provided a is not an argument of a function, including exponents.
# Code
rpsub2:=proc(a,b,arg)
local i,j,prov,prov2,prov3,prov4,ghost,res:
options remember:
prov:=arg:
if not(type(prov,`+`)) then prov:=prov+ghost fi:
res:=0:
for i from 1 to nops(prov) do
        prov2:=op(i,prov):
        prov4:=prov2:
        if type(prov2,`*`) then
                for j from 1 to nops(prov2) do
                        prov3:=op(j,prov2):
                        if prov3=a then
                                prov4:=prov2*b/prov3:
                                j:=nops(prov2)
                        fi
                od:
        else
                if prov2=a then prov4:=b fi
        fi:
        res:=res+prov4
od:
res:=subs(ghost=0,res):
res
end:
# Implementation - Polynomial Symmetries
#
# Returns a list with the first element a polynomial in the variables in vr and
# coefficients depending on variables in dp, with monomial with degrees from n1 to n2.
# the list of coefficients is the set in the second element of the output.
#
build_poly:=proc(n1,n2,vr,dep,nm)
local res,i,k,q,pl,ex,nv,fl,lc,cc,dep2,cfs,nome:
cc:=1:
cfs:={}:
dep2:=op(dep):
pl:=0:
nv:=nops(vr):
if nv=1 then
   for i from n1 to n2 do
       if dep=[] or dep={} then
          nome:=cat(nm,cc)
       else
          nome:=cat(nm,cc)(dep2)
       fi:
       pl:=pl+nome*vr[1]^i:
       cfs:=cfs union {nome}:
       cc:=cc+1
   od:
   RETURN([pl,cfs])
fi:
ex:=array(1..nv-1):
for k from n1 to n2 do
    for i from 1 to nv-1 do
        ex[i]:=0
    od:
    fl:=true:
    while fl do
          lc:=k:
          for i from 1 to nv-1 do
              lc:=lc-ex[i]
          od:
          if lc>=0 then
             if dep=[] or dep={} then
                nome:=cat(nm,cc)
             else
                nome:=cat(nm,cc)(dep2)
             fi:
             pl:=pl+nome*eval(prod('vr[q]^ex[q]',q=1..nv-1))*vr[nv]^lc:
             cfs:=cfs union {nome}:
             cc:=cc+1
          fi:
          ex[1]:=ex[1]+1:
          if ex[1]>k then
             ex[1]:=0:
             if nv>2 then
                ex[2]:=ex[2]+1:
                for i from 2 to nv-2 do
                    if ex[i]>k then
                       ex[i]:=0:
                       ex[i+1]:=ex[i+1]+1
                    fi
                 od
             fi
          fi:
          if ex[nv-1]>k or (ex[1]=0 and nv<=2) then
             fl:=false
          fi:
    od
od:
[pl,cfs]
end:
# Save
end module:

repo := "/home/marciano/simbolico/sade/lib":
startdir := currentdir(repo):
march('create', "./SADE.lib", 500):


savelibname := repo:
savelib('sade');
restart:
# History
# First version - December 1994.
# Adapted to MAPLE 10 and implementation of the package using a module: August 11, 2006
# Adapted to MAPLE 11 - May 2, 2007
# Adapted to MAPLE 14 - August 2010
# Subsequent version for later Maple releases with minor modifications.
# ODSS Module- 14/11/2000
# 21/11/2000 - Solved the bug due to the new output form of pdsolve.
# 20/03/2001 - Modified the routine diffsolve to handle non-linear systems due to unknown functions in the differential equation operator.
# 22/03/2001 - Solution of partial differential equations in one variable.
# 24/03/2001 - Solved the bug in lifdec that considered D[n,m](function)(variables) as independents functions for different n,m.
#                           Solved also some small bugs.
# 27/03/2001 - Extension for solving the symmetry transformations of Differential Equations. New algorithm for resolve().
# 01/10/2003 - Implements the solutions of systems of partial equations in resolve.
# 09/01/2004 - Implements a slight modifications of the resolve routine, to solve first small algebraic system with
#                          at most two terms.
# 26/01/2004 - Solved a bug in equivalence.
# 10/03/2004 - Solved a bug in odesimpv and introduced the routines resolve2 and iint.
# 12/03/2004 - Introduction of the routine ritred and corresponding modifications in resolve.
# 16/03/2004 - Modification of resolve, resolve2 routines and introductions of resolve_basic. Introduction of the use of RIF package.
#                          Modification of odesimpv (introduction of intsimp) to handle simplifications by integration by parts of solutions with integrals.
# 23/03/2004 - Revision of solving routines.
# 12/04/2004 - Revision of solving routines.
# 29/04/2004 - Introduced the routine pdiffsolve.
# 04/01/2007 - Implementation of solution on solver for non-linear overdetermined systems.
# 14/02/2007 - Corrected a bug in algsymp and lifdec.
# 28/02/2007 - Rewrite part of diffsolve.
# 03/05/2007 - Rewrite solution of single term ODE's using singlediffsolve.
# 17/05/2007 - Introduced the use of Janet basis for computing the involutive form of initial determining systems.
# 06/01/2010 - Implementation of a modified progressive Kolchin-Ritt based algorithm for computing integrability conditions.
# Solution of Non-Linear Overdertermined PDEs - 24/01/2010
# January 24, 2010 - First experimental version of nonlindsolve for solving non-linear overdetermined systems of PDEs.
# Symmetries Module - First version March 1st, 1995. 
# Ver 2.0 May 9, 2002. 
# Ver 2.1 November, 3 2003.
# February, 3 2004 - Solved a bug in noether and introduced the option to give the generator of a given symmetry as the fourth argument.
# August, 08 2004 - Implemented a new method to obtain the determining system, with reduction to the orthonomic form.
# Septermber, 26 2005 - Introduced the involutive option in liesymmetries.
# January, 15 2006 - Corrected a bug in infsym to allow non-polinomial equations using coeffgen.
# January, 2007 -Determination of nonclassical symmetries.
# March 06,2007 - Rewrite the code for obtaining determining equations of non-classical symmetries.
# November 15, 2009 - Correct a few bugs in nonclassical symmetries.
# November 24, 2009 - Corrected a bug in infsym to correctly decompose equations not a polynomial in the derivatives of the dependent variables.
# December 12, 2009 -  Computations of adjoint representation map with AdjointRep.
# December 17, 2009 - Introduction of the option idependent in liesymmetries
# December 27, 2009 - Optimization of infsym
# February 4, 2010 - Routine LBsymmetries fot copmuting Lie-Bäcklund symmetries.
# June 5, 2016 - Corretected a small bug in solvehigh,
# QPSI Module - January 2001. Ver 2.2 May 9, 2002.
# October 27, 2003 - Implementation of the Gb package in quasisolve.
# January 05, 2004 - New input sintax using the routine LVformat. Implementation of isQm and isQP.
# January 13,2004 - Rewrite all the code of arrange_solution  and invariant with simplifications with respect to the previous version.
# Standard Form - August 16, 2004.
# PDE Solutions - August 16, 2004.
# Implementation of similarity solutions with Lie Symmetries.
# August 24, 2004 - Implementation of non-classical symmetries.
# November 2009 - Implementation of potential symmetries.
# December 25, 2009 - New implmentation of invariant_sol routine to reduce to PDE of lower dimensionality.
# ODE Solutions - January 13, 2006
# Implemented invariant solutions for ODE's and order reduction with solution for solvabre Liesymmetry algebras.
# Classification - January, 14 2007
# Implementation of the routine equivalence.
# Implementation of invariant solutions using potential symmetries - October 28, 2009
# Implementation o Lie-Bäcklund Symmetries - January 2010.
# Additional optimizations of ODSS - February 2010.
# Implementation of polynomial symmetries intended initially for non-linear fields.
# Test and correction of a minor bugs with Maple 17 - August 2013

# Solving small bugs
# Solved a bug in derived_subalg - 04/05/2023
# 
