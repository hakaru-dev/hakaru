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

# Note that large parts of this are not very nice. It is a very literal
# translation of the code which it replaced, which a very thin amount
# of abstraction on top. But it does the hard work of factoring
# out all of the domain-related code into a single module.
# At some point, the interface should be improved, and the implementation
# should get rid of all sorts of unnecessary conversions.

# Broad TODOs:
# Make bound extraction look into products ('integrate out GammaD with PoissonD likelihood to NegativeBinomial')
#
# Mechanism for 'checking if' and 'making' constraints about variables should
#   be abstracted out into its own module (it is needed in multiple places, and
#   done sort of ad-hoc) (this could be fixed by a broader design - see "merging
#   KB with Domain")
#
# General interface for folding over a domain while including the domain
#   information in a context; basically a function of type
#      (X -> X) -> X where X = DomBound -> DomShape -> r
#   Pretty much everything in Domain does this, or should be doing it! and this
#   insulates against future additions of new constructors which may have
#   'interesting' contexts.
#
# All the global setup should be done through some kind of table
#
# Shape extraction needs to be reworked; we "flatten" constraints multiple
#   times; This should be done once after shape extraction, not at every step
#
# Several 'simplifications' other than LMS are done in LMS. These need to have
#   their own entry in Simplifiers (and work properly in their own context).
#
# DInto should also optionally omit the bounds if they are identical to the
#   bounds in the a-priori domain bounds (i.e. just `DInto(x)`); DInto sort of
#   means 'we've solved this bound in this subcontext' but the `DInto`s where
#   the bound is identically the a-priori bound are erased (as they should be)
#   - we want a slightly seperate form to mean "we are done improving this", but
#   we still want to be able to omit bounds which would be identical. It should
#   also allow specifying only a subset of the bounds.
#
# A mechanism for Bound to use it as a table. In particular, we don't want to
#   represent the bound as a table, but we do "table lookup" on variables quite
#   a bit. (perhaps add a function which places the table as a second component
#   in the bounds, and have the Bound functions use it; or even a big record,
#   containing the table and other things; so long as we update the original
#   bound concurrently with the table, we should be okay with `has`, etc. I
#   believe that another table which provides lookup from names to indices in
#   the list would allow it to be done efficiently?)
#
# A more granular interface for composing/re-composing simplifiers, including
#   call simplifier A {before/after} B
#
# Domain should support Ints/Sums. Currently pretty much all of the hard work is
#   in place; the concept of 'variables' needs to be generalized to 'indexed
#   variables' and 'ranges' to 'collections of ranges'. Perhaps the 'variable'
#   and 'range' types should actually be part of ExtBound, and ExtBound provides
#   a consistent way for dealing with different variable types that have an
#   entirely different syntactic form but essentially identical semantics.
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
# A better interface for `simpl_relation` - something that allows it to treat
#   arbitrary constructor forms as And, Or, Not. Typically, we do a `subs` right
#   before the call to `simpl_relation` to put things in the right form, then
#   another `subs` immediately inside `simpl_relation` to turn `And,Or` into `&and,&or`.
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

Domain := module()
    uses Hakaru, Partition, SolveTools[Inequality] ;
    global DOMAIN; global DBound; global DConstrain; global DSum; global DSplit; global DInto; global DNoSol;

    local ModuleLoad := proc($)
           local ty_nm, g;
           for ty_nm in [ indices(DomainTypes, nolist) ] do
               TypeTools[AddType]( ty_nm, DomainTypes[ty_nm] );
           end do;

           #op([2,6], ...) of a module is its globals.
           for g in op([2,6], thismodule) do
               if g <> eval(g) then
                   unassign(g);
                   WARNING("Previous value of global name '%1' erased.", g)
               end if;
               if assigned(Domain:-GLOBALS[g]) then
                   assign(g = copy(Domain:-GLOBALS[g]));
               end if;
               protect(g);
           end do;

           # unprotect(Domain:-ExtShape);
           # ExtShape[`PARTITION`] :=
           # ExtShape[`piecewise`] :=
           # unprotect(Domain:-ExtShape);
    end proc;

    local ModuleUnload := proc($)
        local ty_nm;
        for ty_nm in [ indices(DomainTypes, nolist) ] do
            if TypeTools[Exists](ty_nm) then TypeTools[RemoveType](ty_nm) end if;
        end do;
    end proc;

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

    export simpl_relation :=
    proc( expr_ :: {relation, boolean, specfunc({`And`,`Not`,`Or`}), `and`, `not`, `or`}
        , { norty := 'DNF' }
        , $) :: { specfunc(specfunc({relation, specfunc(relation, Not)}, `Or`), `And`)
                , specfunc(specfunc({relation, specfunc(relation, Not)}, `And`), `Or`)
                };
        local expr := expr_, outty, outmk, inty, inmk, ty_ord ;

        expr := foldr( proc(v,e) subsindets(e, op(v)) end proc
                     , expr
                     , [ { specfunc(relation, `Not`), `not`(relation) }
                       , x-> KB:-negate_rel(op(1,x)) ]
                     , [ { specfunc(`Not`), `not` }
                       , x->Logic:-`&not`(op(1,x)) ]
                     , [ { specfunc(`Or`), `or` }
                       , x->Logic:-`&or`(op(x)) ]
                     , [ { specfunc(`And`), `and` }
                       , x->Logic:-`&and`(op(x)) ] );
        expr := Logic:-Normalize(expr, form=norty);
        expr := foldr( proc(v,e) subsindets(e, op(v)) end proc
                     , expr
                     , [ specfunc(Logic:-`&and`), x->`And`(op(x)) ]
                     , [ specfunc(Logic:-`&or`) , x->`Or`(op(x)) ]
                     , [ specfunc(Logic:-`&not`), x->KB:-negate_rel(op(1,x))  ] );

        if expr :: identical(false) then
            return `if`(norty='DNF', `Or`(), `And`(`Or`()));
        elif expr :: identical(true) then
            return `if`(norty='DNF', `Or`(`And`()), `And`());
        end if;

        ty_ord := `if`(norty='DNF', [1,2], [2,1]);
        outty, inty := [ 'specfunc(Or)', 'specfunc(And)' ][ty_ord][];
        outmk, inmk := [ `Or`, `And` ][ty_ord][];

        if not expr :: outty then expr := outmk(expr) end if;
        map(x -> if not x :: inty then inmk(x) else x end if, expr);
    end proc;

    export Fold := proc(e0, kb :: t_kb
                , f_into, f_body
                , f_apply
                , f_nosimp := (_->FAIL), $)
      local F_INTO, F_BODY, e := e0, rn
           , dom_specb, dom_specw, dom_ctx, dom_spec1, dom_spec, mkDom ;
      rn := [F_INTO=f_into, F_BODY=f_body,%subs=subs];

      dom_specb, e := op(Domain:-Extract:-Bound(e));
      if Domain:-Bound:-isEmpty(dom_specb) then return f_nosimp(e0) end if;
      dom_specw, e := op(Domain:-Extract:-Shape(e));

      dom_ctx := {op(KB:-kb_to_constraints(kb))};
      dom_specb := DBound(op(1,dom_specb), dom_ctx);
      dom_spec := DOMAIN(dom_specb, dom_specw);

      if dom_specw <> DConstrain() then
        dom_spec := Domain:-Improve(dom_spec);
      end if;

      mkDom := Domain:-Apply(dom_spec, kb, F_INTO, F_BODY);
      e := f_apply(dom_specb, x->eval(mkDom(x),rn), e);
      if has(e, FAIL) then
        # TODO: check for type(e, LO)
        f_nosimp(e0);
      else
        e
      end if;
    end proc;

end module;
