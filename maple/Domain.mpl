### Domain abstraction

# A domain is abstractly a pair of a "square" domain (a product of square
# domains, or an interval), the domain "bounds", and a domain "shape". The
# domain "bounds" are essentially the variables, each with the type of domain
# (Int,Sum, etc) ; the domains "shape" is sums of products of constraints
# (relations) on the domain, interspersed with 'makes' (DInto) which parametrize
# a subdomain by one of the domain variables ('picking' a particular
# parametrization of the domain, in which one variable is fixed in subsequent
# "shape" constructors).

# the seperation between the two 'stages' of domain exists mainly because
# certain simplifications need to happen after extracting the domain
# bounds but before extracting the domain shape, as the shape ends up
# becoming part of the bounds of an inner simplification.

# Broad TODOs:
#
# Mechanism for 'checking if' and 'making' constraints about variables should
#   be abstracted out into its own module (it is needed in multiple places, and
#   done sort of ad-hoc) (this could be fixed by a broader design - see "merging
#   KB with Domain")
#
# DInto should also optionally omit the bounds if they are identical to the
#   bounds in the a-priori domain bounds (i.e. just `DInto(x)`); DInto sort of
#   means 'we've solved this bound in this subcontext' but the `DInto`s where
#   the bound is identically the a-priori bound are erased (as they should be)
#   - we want a slightly seperate form to mean "we are done improving this", but
#   we still want to be able to omit bounds which would be identical. It should
#   also allow specifying only a subset of the bounds.
#
# A more granular interface for composing/re-composing simplifiers, including
#   call simplifier A {before/after} B
#
# Domain bounds should store a representation of 'dependancy' of variables
#   (a more refined representation; the current one is a linear order of variables)
#   Basically we want a list of graphs, nodes are variables and edges are
#   variable dependencies. If each graph is acyclic, the variable dependency
#   in the bounds is valid. e.g.
#     [x=0..1, y=0..1, z=0..1]  =>  [ {[x, {}]}, {[y, {}]}, {[z, {}]} ]
#     [x=0..1, y=x..1, z=0..y]  =>  [ {[z, {y}], [y, {x}], [x, {}]} ]
#   This generalizes the previous notion of variable order, although in certain
#     cases it is ambiguous what the 'original' order was. This is only when
#     there are variable dependencies, so perhaps this isn't a big deal - we may
#     want to rearrange the dependant bounds even when there is no 'interesting'
#     constraint to solve in the shape, because we know a particular order will
#     be better in some way.
#   The graph is probably not a convenient place to store the variable bounds.
#    (this is one of the big reasons we want to view the variables as a table -
#    we have lots of different information for which the convenient formats are
#    all different)
#
# Long term, KB and Domain should be merged, as their functionality overlaps
#   quite a bit; basically
#     - Introduce becomes a variable in DBound
#     - Constrain becomes DConstrain
#     - DBound becomes DInto
#     - Let becomes (probably?) a one piece partition,
#           or maybe a new variable type
#          (it doesn't seem to appear in present code?)
#  Logically, this is at most an ephemeral change - Domain already generalizes
#   KB. But mechanically it is no small undertaking.
#  assert_deny becomes a "DConstrain" smart constructor (note that in the
#   current AST for Domain, DConstrain appears only at leaves, i.e. products
#   are pushed all the way down; whereas KB is 'flat') but the shape of domains
#   means it is probably much simpler to 'normalize' the constraints all at
#   once, as opposed to when every constrain is inserted, as KB currently does.
#  kb_subtract becomes a similar `domain_combine` function (kb_subtract is really
#   an 'combine' as well as a 'deconstruct into a way to rebuild the KB' together in
#   one - we don't really need the 'deconstruct' part anymore, but 'add' is
#   still useful) - basically this function takes two domains, checks if the
#   variables of the first are a subset of the second (non commutative!) and if
#   so, combines the shapes according to the passed 'shape constructor'; all of
#   the constructors (aside from DInto)
#  gen{whatever} becomes a part of `Domain:-Extract` - basically we will not
#   have `gen` as part of the "interface" to KB+Domain, but rather an entry in
#   the `Ext` function tables.
#  most of the other functions in KB can be basically literally translated to
#    the subset of Domain which corresponds to KB

# The `Domain' type, i.e., its constructors. For a description of the
# intended semantics (as an algebraic datatype), see Domain/Types.mpl
Domain_Type := module()
  option package;
  export
    DOMAIN, DBound, DConstrain, DSum,
    # These intentionally have no definition
    DSplit, DInto, DNoSol;

  DOMAIN := proc()
    local errs := indets([args[2..-1]], specfunc(`DNoSol`));
    if errs <> {} then
      'procname'(args[1], 'DNoSol'(map(op,errs)[]));
    end if;
    'procname'(args);
  end proc;

  DBound := proc(a)
    local b,cs;
    b := `if`(nargs>=2,[args[2]],[KB:-empty])[];
    cs := `if`(nargs>=3,[args[3..-1]],[])[];
    'procname'(a,b,cs) ;
  end proc;

  DConstrain := proc()
    local as := {args};
    if false in as then return DSum() end if;
    as := remove(x->x::identical(false),as);
    'procname'(op(as));
  end proc;

  DSum := proc()
    local as := [args];
    as := subsindets(as, specfunc(`DSum`), xs->
                     map(x->if op(0,x)=`DSum` then op(x) else x end if,
                         xs));
    if nops(as) = 1 then return op(1,as) end if;
    'procname'(op(as));
  end proc;
end module;

Domain := module()
    uses Hakaru, Utilities, Partition, SolveTools[Inequality], Domain_Type ;

    local ModuleLoad := proc($)
      local g;
      BindingTools:-load_types_from_table(DomainTypes);

      #op([2,6], ...) of a module is its globals.
      for g in op([2,6], thismodule) do
        if g <> eval(g) then
          unassign(g);
          WARNING("Previous value of global name '%1' erased.", g)
        end if;
        protect(g);
      end do;
      Apply:-ModuleLoad(); # Needed to load types properly (?)
    end proc;

    local ModuleUnload := proc($) NULL; end proc;

    # Extending domain extraction and replacement.
    export ExtBound := table();
    export ExtShape := table();

    export Set_ExtBound := proc(nm,val,$)
      unprotect(Domain:-ExtBound);
      Domain:-ExtBound[nm] := val;
      protect(Domain:-ExtBound);
    end proc;

    export Set_ExtShape := proc(nm,val,$)
      unprotect(Domain:-ExtShape);
      Domain:-ExtShape[nm] := val;
      protect(Domain:-ExtShape);
    end proc;

$include "Domain/Has.mpl"
$include "Domain/Bound.mpl"
$include "Domain/Shape.mpl"
$include "Domain/Types.mpl"
$include "Domain/Extract.mpl"
$include "Domain/Apply.mpl"
$include "Domain/Improve.mpl"

    local default_handlers :=
      Record('f_apply'=((f,x)->f(x)), 'f_nosimp'=(_->FAIL));

    # The main interface to Domain
    export Reduce :=
      proc(e0,dom_ctx::t_kb,handlers0,opts:=[],$)
      local e := e0, dom_specb, dom_specw, dom_spec, dom_ctx1, rn, ws
          , handlers := merge_record_default(default_handlers, handlers0)
          , apply_ctx ;

      # Build the domain
      dom_specb, e, ws := op(Domain:-Extract:-Bound(e));
      if Domain:-Bound:-isEmpty(dom_specb)
      then return handlers:-f_nosimp(e0) end if;
      dom_ctx1, rn := Domain:-Bound:-toKB(dom_specb)[];
      dom_specb, e, ws := subs(rn,[dom_specb,e,ws])[];
      dom_specw, e := op(Domain:-Extract:-Shape(e, dom_ctx1));
      dom_specb := DBound(op(1,dom_specb), dom_ctx);
      dom_spec := DOMAIN(dom_specb, dom_specw);

      # Improve, if necessary, then apply back to the expression
      if dom_specw <> DConstrain() and not ("no_domain" in {opts[]})
      then dom_spec := Domain:-Improve(dom_spec) end if;

      apply_ctx := Record[handlers]('weights'=table(ws),-'f_apply',-'f_nosimp');
      handlers:-f_apply(Domain:-Apply(dom_spec, apply_ctx), e);
    end proc;

    ModuleLoad();
end module;
