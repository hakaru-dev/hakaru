# Teach Maple (through depends and eval) about our new binding forms.
# lam binds from 1st arg to 3rd arg.
# Branch binds from 1st arg (a pattern) to 2nd arg.
# Bind and ary bind from 2nd arg to 3rd arg.

# note that v _can_ in principle occur in t.
`depends/lam` := proc(v::name, t, e, x, $)
  depends(t, x) or depends(e, x minus {v})
end proc:

`depends/Branch` := proc(p, e, x, $)
  depends(e, x minus {Hakaru:-pattern_binds(p)})
end proc:

# note that v _can_ occur in m1.
`depends/Bind` := proc(m1, v::name, m2, x, $)
  depends(m1, x) or depends(m2, x minus {v})
end proc:

# note that i _can_ occur in n.
`depends/ary` := proc(n, i::name, e, x, $)
  depends(n, x) or depends(e, x minus {i})
end proc:
`depends/Plate` := eval(`depends/ary`):

`eval/lam` := proc(e, eqs, $)
  local v, t, ee;
  v, t, ee := op(e);
  v, ee := BindingTools:-generic_evalat(v, ee, eqs);
  t := eval(t, eqs);
  eval(op(0,e), eqs)(v, t, ee)
end proc:

`eval/Branch` := proc(e, eqs, $)
  local p, ee, vBefore, vAfter;
  p, ee := op(e);
  vBefore := [Hakaru:-pattern_binds(p)];
  vAfter, ee := BindingTools:-generic_evalat(vBefore, ee, eqs);
  eval(op(0,e), eqs)(subs(op(zip(`=`, vBefore, vAfter)), p), ee)
end proc:

`eval/Bind` := proc(e, eqs, $)
  local m1, v, m2;
  m1, v, m2 := op(e);
  eval(op(0,e), eqs)(eval(m1, eqs), BindingTools:-generic_evalat(v, m2, eqs))
end proc:

`eval/ary` := proc(e, eqs, $)
  local n, i, ee;
  n, i, ee := op(e);
  eval(op(0,e), eqs)(eval(n, eqs), BindingTools:-generic_evalat(i, ee, eqs))
end proc:
`eval/Plate` := eval(`eval/ary`):

#############################################################################

Hakaru := module ()
  option package;
  local p_true, p_false, make_piece, lift1_piecewise,
        ModuleLoad, ModuleUnload;
  export
     # These first few are smart constructors (for themselves):
         case, app, ary, idx, size, Datum,
     # while these are "proper functions"
         verify_measure, pattern_equiv,
         piecewise_And, map_piecewiselike, lift_piecewise, foldr_piecewise,
         pattern_match, pattern_binds,
         closed_bounds, open_bounds,
         htype_patterns;
  # These names are not assigned (and should not be).  But they are
  # used as global names, so document that here.
  global
     # Basic syntax for composing measures
         Bind, Weight, Ret, Msum, Plate, Context,
     # Primitive (known) measures
         Lebesgue, Uniform, Gaussian, Cauchy, StudentT, BetaD,
         GammaD, ChiSquared,
         Counting, Categorical, NegativeBinomial, PoissonD,
     # Functions, annotated with argument type, applied using "app"
         lam,
     # Term constructors for Datum (algebraic data type)
         Inr, Inl, Et, Done, Konst, Ident,
     # The parts of "case" besides the scrutinee
         Branches, Branch,
     # Pattern constructors
         PWild, PVar, PDatum, PInr, PInl, PEt, PDone, PKonst, PIdent,
     # Verification of alpha-equivalence among measures
         measure,
     # Structure types for Hakaru types and Hakaru "case" expressions
         t_type, t_case,
     # Structure types for piecewise-like expressions:
     # piecewise, case, and idx into literal array
         t_piecewiselike,
     # Type constructors for Hakaru
         AlmostEveryReal, HReal, HInt, HData, HMeasure, HArray, HFunction,
         Bound, DatumStruct;

  p_true  := 'PDatum(true,PInl(PDone))';
  p_false := 'PDatum(false,PInr(PInl(PDone)))';

  case := proc(e, bs :: specfunc(Branch(anything, anything), Branches), $)
    local ret, b, substs, eSubst, pSubst, p, binds, uncertain;
    if e :: 't_piecewiselike' then
      map_piecewiselike(procname, _passed)
    else
      ret := Branches();
      for b in bs do
        substs := pattern_match(e, e, op(1,b));
        if substs <> NULL then
          eSubst, pSubst := substs;
          p := subs(pSubst, op(1,b));
          binds := {pattern_binds(p)};
          uncertain := remove((eq -> lhs(eq) in binds), eSubst);
          if nops(uncertain) = 0 then p := PWild end if;
          ret := Branches(op(ret),
                          Branch(p, eval(eval(op(2,b), pSubst), eSubst)));
          if nops(uncertain) = 0 then break end if;
        end if
      end do;
      if ret :: Branches(Branch(identical(PWild), anything)) then
        op([1,2], ret)
      elif ret :: Branches(Branch(identical(p_true), anything),
                           Branch({identical(p_false),
                                   identical(PWild),
                                   PVar(anything)}, anything)) then
        piecewise(make_piece(e), op([1,2], ret), op([2,2], ret))
      elif ret :: Branches(Branch(identical(p_false), anything),
                           Branch({identical(p_true),
                                   identical(PWild),
                                   PVar(anything)}, anything)) then
        piecewise(make_piece(e), op([2,2], ret), op([1,2], ret))
      else
        'case'(e, ret)
      end if
    end if
  end proc;

  pattern_match := proc(e0, e, p, $)
    local x, substs, eSubst, pSubst;
    if p = PWild then return {}, {}
    elif p :: PVar(anything) then
      x := op(1,p);
      pSubst := {`if`(depends(e0,x), x=gensym(x), NULL)};
      return {subs(pSubst,x)=e}, pSubst;
    elif p = p_true then
      if e = true then return {}, {}
      elif e = false then return NULL
      end if
    elif p = p_false then
      if e = false then return {}, {}
      elif e = true then return NULL
      end if
    elif p :: PDatum(anything, anything) then
      if e :: Datum(anything, anything) then
        if op(1,e) = op(1,p) then return pattern_match(e0, op(2,e), op(2,p))
        else return NULL
        end if
      end if
    elif p :: PInl(anything) then
      if e :: Inl(anything) then return pattern_match(e0, op(1,e), op(1,p))
      elif e :: Inr(anything) then return NULL
      end if
    elif p :: PInr(anything) then
      if e :: Inr(anything) then return pattern_match(e0, op(1,e), op(1,p))
      elif e :: Inl(anything) then return NULL
      end if
    elif p :: PEt(anything, anything) then
      if e :: Et(anything, anything) then
        substs := pattern_match(e0, op(1,e), op(1,p));
        if substs = NULL then return NULL end if;
        eSubst, pSubst := substs;
        substs := pattern_match(e0, eval(op(2,e),eSubst), op(2,p));
        if substs = NULL then return NULL end if;
        return eSubst union substs[1], pSubst union substs[2];
      elif e = Done then return NULL
      end if
    elif p = PDone then
      if e = Done then return {}, {}
      elif e :: Et(anything, anything) then return NULL
      end if
    elif p :: PKonst(anything) then
      if e :: Konst(anything) then return pattern_match(e0, op(1,e), op(1,p))
      end if
    elif p :: PIdent(anything) then
      if e :: Ident(anything) then return pattern_match(e0, op(1,e), op(1,p))
      end if
    else
      error "pattern_match: %1 is not a pattern", p
    end if;
    pSubst := map((x -> `if`(depends(e0,x), x=gensym(x), NULL)),
                  {pattern_binds(p)});
    eSubst := {e=subsindets(
                   subsindets[nocache](
                     subs(pSubst,
                          p_true=true,
                          p_false=false,
                          PDatum=Datum, PInr=Inr, PInl=Inl, PEt=Et, PDone=Done,
                          PKonst=Konst, PIdent=Ident,
                          p),
                     identical(PWild),
                     p -> gensym(_)),
                   PVar(anything),
                   p -> op(1,p))};
    eSubst, pSubst
  end proc;

  make_piece := proc(rel, $)
    # Try to prevent PiecewiseTools:-Is from complaining
    # "Wrong kind of parameters in piecewise"
    if rel :: {specfunc(anything, {And,Or,Not}), `and`, `or`, `not`} then
      map(make_piece, rel)
    elif rel :: {'`::`', 'boolean', '`in`'} then
      rel
    else
      rel = true
    end if
  end proc;

  pattern_binds := proc(p, $)
    if p = PWild or p = PDone then
      NULL
    elif p :: PVar(anything) then
      op(1,p)
    elif p :: PDatum(anything, anything) then
      pattern_binds(op(2,p))
    elif p :: {PInl(anything), PInr(anything),
               PKonst(anything), PIdent(anything)} then
      pattern_binds(op(1,p))
    elif p :: PEt(anything, anything) then
      pattern_binds(op(1,p)), pattern_binds(op(2,p))
    else
      error "pattern_binds: %1 is not a pattern", p
    end if
  end proc:

  verify_measure := proc(m, n, v:='boolean', $)
    local mv, x, i, j, k;
    mv := measure(v);
    if m :: specfunc({Bind, Plate}) and n :: specfunc({Bind, Plate}) and
       (verify(m, n, 'Bind'(mv, true, true))
      or verify(m, n, 'Plate'(v, true, true))) then
      x := gensym(cat(op(2,m), "_", op(2,n), "_"));
      thisproc(subs(op(2,m)=x, op(3,m)),
               subs(op(2,n)=x, op(3,n)), v)
    elif m :: 'specfunc(Msum)' and n :: 'specfunc(Msum)'
         and nops(m) = nops(n) then
      k := nops(m);
      verify(k, GraphTheory[BipartiteMatching](GraphTheory[Graph]({
                seq(seq(`if`(thisproc(op(i,m), op(j,n), v), {i,-j}, NULL),
                        j=1..k), i=1..k)}))[1]);
    elif andmap(type, [m,n], 'specfunc(piecewise)') and nops(m) = nops(n) then
      k := nops(m);
      verify(m, n, 'piecewise'(seq(`if`(i::even or i=k, mv, v), i=1..k)))
    elif m :: specfunc('case') and 
        verify(m, n, 'case'(v, specfunc(Branch(true, true), Branches))) then
      # This code unfortunately only handles alpha-equivalence for 'case' along
      # the control path -- not if 'case' occurs in the argument to 'Ret', say.
      k := nops(op(2,m));
      for i from 1 to k do
        j := pattern_equiv(op([2,i,1],m), op([2,i,1],n));
        if j = false then return j end if;
        j := map(proc(eq, $)
                   local x;
                   x := gensym(cat(lhs(eq), "_", rhs(eq), "_"));
                   [lhs(eq)=x, rhs(eq)=x]
                 end proc, j);
        j := thisproc(subs(map2(op,1,j), op([2,i,2],m)),
                      subs(map2(op,2,j), op([2,i,2],n)), v);
        if j = false then return j end if;
      end do;
      true
    elif m :: 'LO(name, anything)' and n :: 'LO(name, anything)' then
      x := gensym(cat(op(1,m), "_", op(1,n), "_"));
      verify(subs(op(1,m)=x, op(2,m)),
             subs(op(1,n)=x, op(2,n)), v)
    elif m :: specfunc('lam') and n :: specfunc('lam') and
        verify(m, n, 'lam'(true, v, true)) then
      # m and n are not even measures, but we verify them anyway...
      x := gensym(cat(op(1,m), "_", op(1,n), "_"));
      thisproc(subs(op(1,m)=x, op(2,m)),
               subs(op(1,n)=x, op(2,n)), v)
    else
      verify(m, n, {v, Ret(v), Weight(v, mv), Context(v, mv)})
    end if
  end proc;

  pattern_equiv := proc(p, q, $) :: {identical(false),set(`=`)};
    local r, s;
    if ormap((t->andmap(`=`, [p,q], t)), [PWild, PDone]) then
      {}
    elif andmap(type, [p,q], PVar(anything)) then
      {op(1,p)=op(1,q)}
    elif andmap(type, [p,q], PDatum(anything,anything)) and op(1,p)=op(1,q) then
      pattern_equiv(op(2,p),op(2,q))
    elif ormap((t->andmap(type, [p,q], t(anything))),
               [PInl, PInr, PKonst, PIdent]) then
      pattern_equiv(op(1,p),op(1,q))
    elif andmap(type, [p,q], PEt(anything, anything)) then
      r := pattern_equiv(op(1,p),op(1,q));
      s := pattern_equiv(op(2,p),op(2,q));
      if map(lhs,r) intersect map(lhs,s) = {} and
         map(rhs,r) intersect map(rhs,s) = {} then
        r union s
      else
        false
      end if
    else
      false
    end if
  end proc;

  piecewise_And := proc(cond::list, th, el, $)
    if nops(cond) = 0 or th = el then
      th
    else
      piecewise(And(op(cond)), th, el)
    end if
  end proc;

  map_piecewiselike := proc(f, p::t_piecewiselike)
    local i, g, h;
    if p :: 'specfunc(piecewise)' then
      piecewise(seq(`if`(i::even or i=nops(p), f(op(i,p),_rest), op(i,p)),
                    i=1..nops(p)))
    elif p :: 't_case' then
      # Mind the hygiene
      subsindets(eval(subsop(2 = map[3](applyop, g, 2, op(2,p)), p),
                      g=h(f,_rest)),
                 'typefunc(specfunc(h))',
                 (e -> op([0,1],e)(op(1,e), op(2..-1,op(0,e)))))
    elif p :: 'idx(list, anything)' then
      idx(map(f,op(1,p),_rest), op(2,p))
    else
      error "map_piecewiselike: %1 is not t_piecewiselike", p
    end if
  end proc;

  lift_piecewise := proc(e, extra:={}, $)
    local e1, e2;
    e2 := e;
    while e1 <> e2 do
      e1 := e2;
      e2 := subsindets(e1,
              '{extra,
                And(`+`, Not(specop(Not(specfunc(piecewise)), `+`))),
                And(`*`, Not(specop(Not(specfunc(piecewise)), `*`))),
                And(`^`, Not(specop(Not(specfunc(piecewise)), `^`))),
                exp(specfunc(piecewise))}',
              lift1_piecewise)
    end do
  end proc;

  lift1_piecewise := proc(e, $)
    local i, p;
    if membertype(t_piecewiselike, [op(e)], i) then
      p := op(i,e);
      if nops(p) :: even and not (e :: `*`) and op(-1,p) <> 0 then
        p := piecewise(op(p), 0);
      end if;
      map_piecewiselike((arm->lift1_piecewise(subsop(i=arm,e))), p)
    else
      e
    end if
  end proc;

  foldr_piecewise := proc(cons, nil, pw, $) # pw may or may not be piecewise
    # View pw as a piecewise and foldr over its arms
    if pw :: 'specfunc(piecewise)' then
      foldr(proc(i,x) cons(op(i,pw), op(i+1,pw), x) end proc,
            `if`(nops(pw)::odd, cons(true, op(-1,pw), nil), nil),
            seq(1..nops(pw)-1, 2))
    else
      cons(true, pw, nil)
    end if
  end proc;

  app := proc (func, argu, $)
    if func :: 'lam(name, anything, anything)' then
      eval(op(3,func), op(1,func)=argu)
    elif func :: 't_piecewiselike' then
      map_piecewiselike(procname, _passed)
    else
      'procname(_passed)'
    end if
  end proc;

  ary := proc (n, i, e, $)
    local j;
    if e :: 'idx'('freeof'(i), 'identical'(i)) then
      # Array eta-reduction. Assume the size matches.  (We should keep array
      # size information in the KB and use it here, but we don't currently.)
      op(1,e)
    elif n :: nonnegint then
      [seq(eval(e,i=j), j=0..n-1)] # Unroll array with literal size
    else
      'procname(_passed)'
    end if
  end proc;

  idx := proc (a, i, $)
    if a :: 'ary(anything, name, anything)' then
      eval(op(3,a), op(2,a)=i)
    elif a :: 'list' and i::nonnegint then
      a[i+1]
    elif a :: 'list' and nops(convert(a,'set')) = 1 then
      a[1] # Indexing into a literal array whose elements are all the same
    elif a :: 't_piecewiselike' then
      map_piecewiselike(procname, _passed)
    else
      'procname(_passed)'
    end if
  end proc;

  size := proc(a, $)
    local res;
    if a :: 'ary(anything, name, anything)' then
      op(1,a)
    elif a :: 'list' then
      nops(a)
    elif a :: 't_piecewiselike' then
      map_piecewiselike(procname, _passed)
    else
      'procname(_passed)'
    end if
  end proc;

  Datum := proc(hint, payload, $)
    # Further cheating to equate Maple booleans and Hakaru booleans
    if hint = true and payload = Inl(Done) or
       hint = false and payload = Inr(Inl(Done)) then
      hint
    else
      'procname(_passed)'
    end if
  end proc;

  closed_bounds := proc(r::range, $)
    Bound(`>=`, lhs(r)), Bound(`<=`, rhs(r))
  end proc;

  open_bounds := proc(r::range, $)
    Bound(`>`, lhs(r)), Bound(`<`, rhs(r))
  end proc;

  # Enumerate patterns for a given Hakaru type
  htype_patterns := proc(t::t_type, $)
    :: specfunc(Branch(anything, list(t_type)), Branches);
    local struct;
    uses StringTools;
    if t :: specfunc(DatumStruct(anything, list(Konst(anything))), HData) then
      foldr(proc(struct,ps,$) Branches(
              op(map((p -> Branch(PDatum(op(1,struct), PInl(op(1,p))),
                                  op(2,p))),
                     foldr(proc(kt,qs,$)
                             local p, q;
                             Branches(seq(seq(Branch(PEt(PKonst(op(1,p)),
                                                         op(1,q)),
                                                     [op(op(2,p)),op(op(2,q))]),
                                              q in qs),
                                          p in htype_patterns(op(1,kt))))
                           end proc,
                           Branches(Branch(PDone, [])), op(op(2,struct))))),
              op(map[3](applyop, PInr, [1,2], ps)))
            end proc,
            Branches(), op(t))
    else
      Branches(Branch(PVar(gensym(convert(LowerCase(op(-1, ["x", op(
                                            `if`(t::function,
                                              select(IsUpper, Explode(op(0,t))),
                                              []))])),
                                          name))),
                      [t]))
    end if
  end proc;

  ModuleLoad := proc($)
    VerifyTools[AddVerification](measure = eval(verify_measure));
    TypeTools[AddType](t_type,
      '{specfunc(Bound(identical(`<`,`<=`,`>`,`>=`), anything),
                 {AlmostEveryReal, HReal, HInt}),
        specfunc(DatumStruct(anything, list({Konst(t_type), Ident(t_type)})),
                 HData),
        HMeasure(t_type),
        HArray(t_type),
        HFunction(t_type, t_type)}');
    TypeTools[AddType](t_case,
      'case(anything, specfunc(Branch(anything, anything), Branches))');
    TypeTools[AddType](t_piecewiselike,
      '{specfunc(piecewise), t_case, idx(list, anything)}');
  end proc;

  ModuleUnload := proc($)
    TypeTools[RemoveType](t_piecewiselike);
    TypeTools[RemoveType](t_case);
    TypeTools[RemoveType](t_type);
    VerifyTools[RemoveVerification](measure);
  end proc;

  ModuleLoad();

end module; # Hakaru
