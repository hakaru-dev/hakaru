  ReparamDetermined := proc(lo :: LO(name, anything))
    local h;
    h := op(1,lo);
    LO(h,
       evalindets(op(2,lo),
                  'And'('specfunc({Int,int})',
                        'anyfunc'(anything, 'name=anything')),
                  g -> `if`(determined(op(1,g),h), Reparam(g,h), g)))
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
       u::name:= gensym('u'),  #new variable of integration
       s,                      #What x will become
       F                       #Boolean: flip integral?
  ;
       s:= {solve({u = target}, {x})};
       if nops(s) = 0 then
            userinfo(1, reparam, "Can't solve substitution target.");
            return e
       end if;
       if nops(s) > 1 then
            userinfo(1, reparam, "Case of multi-branched substitution not handled.");
            return e
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
  reparam:= proc(e::LO(symbol, algebraic), {ctx::list:= []}, $)
  local
       J:= innermostIntSum(e),   #the integral or sum
       newJ, #What J will become
       #possible subs target(s)
       oldarg::{algebraic, set(algebraic)}:= map2(op, 2, indets(e, specfunc(applyintegrand)))
  ;
       if nops(J) = 0 then
            userinfo(2, procname, "No sum or integral found.");
            return e
       end if;
       if nops(J) > 1 then
            userinfo(1, reparam, "Case of multiple innermost Int or Sums not yet handled.");
            return 'procname'(e)
       end if;
       J:= J[];
       if J::specfunc(Sum) then
            userinfo(1, reparam, "Sums not yet handled.");
            return 'procname'(e)
       end if;

       if nops(oldarg) <> 1 then
            userinfo(1, thisproc, "More than 1 reparam possible:", oldarg);
            return 'procname'(e)
       end if;
       oldarg:= oldarg[];   #Extract the reparam target.

       #If the target is simply a name, return input unchanged.
       if oldarg::symbol then
            userinfo(2, procname, "No need for a reparameterization.");
            return e
       end if;

       (*#************ This isn't currently used. **********************************
       #Check the invertibility of the change of vars.

       #The ability of `solve` to select a branch is very limited. For example,
               solve({y=x^2, x > 0}, {x})
       #returns
               sqrt(y), -sqrt(y).
       #This needs to be dealt with. First idea: Use `is` to filter
       #solutions. This is implemented below.

       #The next command is redundantly performed in the local inits. I put it here also
       #because I anticipate some future situations where that's no longer valid.

       #Save current vars for comparison with vars after `solve`.
       Ns:= indets(oldarg, symbol);
       #The usage of `explicit` in the next line is undocumented.
       S:= {solve({'y'=oldarg, a <= x, x <= b}, {x}, allsolutions, explicit)};
       S:= map(s->`if`(s::specfunc(piecewise), s[], s), S);
       #Use `is` to filter solutions under the assumptions.
       assume(a <= x, x <= b);
       S:= select(s-> ver(rhs,lhs)(eval(s, y= oldarg)[]), S);
       if  nops(S) <> 1  or  indets(S, symbol) <> Ns union {y}  or  hastype(S, RootOf)  then
            WARNING("Reparam target is not invertible (upto `solve` and `is`).");
            userinfo(1, procname, "Target:", subs(x= ':-x', oldarg), "S:", subs(x= ':-x', S), "domain:", ':-x'= a..b);
            return 'procname'(e)
       end if;
       *******************************************************************************)

       #Make the change of vars.
       newJ:= simplify_assuming('ChangeVarInt(J, oldarg)', foldr(assert, empty, ctx[]));

       if newJ = 0 then
            WARNING("Integral is 0, likely due to improper handling of an infinity issue.");
            userinfo(
                 1, procname, "u subs:",
                 print(
                      #Reformat the ChangeVarInt command for readability.
                      subs(
                           x= ':-x',
                           'ChangeVarInt'(
                                subsindets(
                                     J,
                                     specfunc(applyintegrand),
                                     f-> ':-h'(op(2,f))
                                )
                           ),
                           oldarg
                      )
                 )
            )
       end if;

       subs(J= newJ, e)
  end proc;
