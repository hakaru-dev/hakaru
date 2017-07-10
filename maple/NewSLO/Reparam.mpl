  ReparamDetermined := proc(lo :: LO(name, anything), kb::t_kb)
    local h;
    h := op(1,lo);
    LO(h,
       evalindets(op(2,lo),
                  'And'('specfunc({Int,int})',
                        'anyfunc'(anything, 'name=anything')),
                  g -> `if`(determined(op(1,g),h), reparam(g,h,kb), g)))
  end proc;

  determined := proc(e, h :: name)
    local i;
    for i in indets(e, 'specfunc({Int,int})') do
      if hastype(IntegrationTools:-GetIntegrand(i),
           'applyintegrand'('identical'(h),
             'dependent'(IntegrationTools:-GetVariable(i)))) then
        return false
      end if
    end do;
    return true
  end proc;

  #Beginning of Carl's code devoted to disintegration and the reparametrization (aka change
  #of variables) of integrals and sums.

  #Finds the innermost Ints or Sums in an expression, that is, those which
  #don't contain further Ints or Sums
  innermostIntSum:= proc(e::anything, $)::set(specfunc({Int,Sum}));
    select(IS-> nops(indets(IS, specfunc({Int,Sum}))) = 1, indets(e, specfunc({Int,Sum})))
  end proc;

  #my substitute for IntegrationTools:-Change
  ChangeVarInt:= proc(J::specfunc(Int), target::algebraic, $)
    local
    newJ, #What J will become.
    x::name:= op([2,1], J),
    u::name:= gensym(x),    #new variable of integration
    s,                      #What x will become
    F                       #Boolean: flip integral?
    ;
    s:= {solve({u = target}, {x})};
    if nops(s) = 0 then
      userinfo(1, 'reparam', "Can't solve substitution target.");
      return J
    end if;
    if nops(s) > 1 then
      userinfo(1, 'reparam', "Case of multi-branched substitution not handled.");
      return J
    end if;
    s:= s[];

    newJ:= Int(
      eval(implicitdiff(u = target, x, u)*op(1,J), s),
      u=
      limit(target, x= op([2,2,1], J), right).. #lower limit
      limit(target, x= op([2,2,2], J), left),   #upper limit
      op(3.., J) #optional Int args (unlikely to be used)
      );

    #If lower limit > upper limit, then flip limits of integration.
    F:= is(op([2,2,1], newJ) > op([2,2,2], newJ));
    if F::truefalse then
      if F then
        userinfo(2, reparam, "Switching limits:", op([2,2], newJ));
        newJ:= IntegrationTools:-Flip(newJ)
      end if
    else #If inequality can't be decided, then don't reverse.
      userinfo(1, reparam, "Can't order new limits:", op([2,2], newJ))
    end if;
    newJ
  end proc;

  #main procedure for int/sum reparamterizations
  reparam:= proc(e::algebraic, h::symbol, ctx::{list,t_kb}:= [], $)
    local
    J:= innermostIntSum(e),   #the integral or sum
    newJ, #What J will become possible subs target(s)
    oldarg:=
    map2(op, 2, indets(e, specfunc(applyintegrand))),
    kb := build_kb(ctx,"reparam"),
    newarg, Jbnds, del
    ;
    if not(oldargs::{algebraic, set(algebraic), list(algebraic)}) then
      userinfo(2, 'procname', "Unexpected arguements to applyintegrand");
      return e;
    end if;
    if nops(J) = 0 then
      userinfo(2, 'procname', "No sum or integral found.");
      return e
    end if;
    if nops(J) > 1 then
      userinfo(1, 'procname', "Case of multiple innermost Int or Sums not yet handled.");
      return e
    end if;
    J:= J[];
    if J::specfunc(Sum) then
      userinfo(1, 'procname', "Sums not yet handled.");
      return e
    end if;
    if hastype(op(1,J), t_pw_or_part) then
      userinfo(1, 'procname', "Reparam of piecewise body not yet handled.");
      return e;
    end if;
    if nops(oldarg) <> 1 then
      userinfo(1, 'procname', "More than 1 reparam possible:", oldarg);
      return e
    end if;
    oldarg:= oldarg[];   #Extract the reparam target.

    Jbnds := op([2,2], J);
    del := simplify_assuming(op(2,Jbnds)-op(1,Jbnds), kb);
    if del in {-1,1} then
      userinfo(2, 'procname', "No need for a reparameterization (bound diff is 1).");
      return e;
    end if;
    if has(Jbnds, infinity) then
      userinfo(2, 'procname', "Reparam of infinity bounds probably won't work.");
      return e;
    end if;

    # if the arg to applyintegrand is not a variable or a datum or an index
    # into an array
    if oldarg::And(Not({symbol, function, indexed, list})) then
      newarg := oldarg;
    # if the bounds don't contain infinity, do not have a difference of 1
    # and contain a product of that variable
    elif oldarg::symbol and
         op(1,J)::`*`   and
         select(type, [op(op(1,J))], identical(oldarg))<>[]
    then
      newarg := oldarg/del;
    else
      userinfo(2, 'procname', "No need for a reparameterization.");
      return e
    end if;

    #Make the change of vars.
    newJ:= kb_assuming_mb(ChangeVarInt@op, [J, newarg], kb, _->FAIL);

    if newJ = 0 or not(newJ::specfunc(Int)) or newJ=FAIL then
      userinfo(
        1, 'procname',
        printf(
          "Invalid reparam, likely due to improper handling of an infinity issue.\n"
          "u subs:%a",
          #Reformat the ChangeVarInt command for readability.
          subs(
            x= ':-x',
            'ChangeVarInt'(
              subsindets(
                J,
                   specfunc(applyintegrand),
                f-> ':-h'(op(2,f)))),
            newarg)));
      return e;
    end if;
    subs(J= newJ, e)
  end proc;
