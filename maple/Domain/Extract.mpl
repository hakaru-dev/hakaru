# Extract a domain from an expression
export Extract := module ()
    export ModuleApply := proc(e, kb, $) :: [ HDomain, anything ];
        local b, eb, s, es;
        b, eb := op(Bound(e));
        s, es := op(Shape(eb, kb ));
        [ DOMAIN(b, s), es ];
    end proc;

    # Extract a domain bound from an expression
    # This pops off the integration constructors recursively, keeping
    # track of the bounds in a KB (which literally become the DBound).
    export Bound := module ()
        export ModuleApply := proc(e, $) :: [ DomBound, anything ];
            local arg, vars, kb;
            arg, vars := do_extract(e)[];
            vars := Domain:-Bound:-withVarsIxs(DBound(vars));
            [ vars , arg ];
        end proc;

        local do_extract_arg := proc(kind, arg_, bound, $)
            local x0, x, vars, arg := arg_, rng;
            x0  := ExtBound[kind]:-ExtractVar(bound);   # variable name
            rng := ExtBound[kind]:-ExtractRange(bound); # variable range
            x   := DInto(x0, rng, kind);                # the variable spec
            arg, vars := do_extract(arg)[];
            [ arg, [ op(vars), x ] ];
        end proc;

        local do_extract := proc(arg, $)
            local sub, prod, svars;
            # if arg :: `*` then
            #     sub := map(do_extract, [op(arg)]);
            #     prod, svars := selectremove(x->op(2,x)=[],sub);
            #     if nops(svars) = 1 then
            #         [ `*`(op([1,1],svars),op(map2(op,1,prod)))
            #         , op([1,2], svars) ];
            #     else
            #         [ arg, [] ];
            #     end if;
            if Domain:-Has:-Bound(arg) then
                do_extract_arg(op(0,arg), op(arg));
            else
                [ arg, [] ]
            end if;
        end proc;
    end module;

    # Extract a domain shape from an expression
    # This extracts the domain shape from individual multiplicands of
    # expressions, and multiplies the subexpressions back together.
    # essentially this assumes a distributive law (of domain shapes over
    # products)
    export Shape := module ()
        export ModuleApply := proc(e) :: [ anything, anything ];
            local ixs, w, e1;
            ixs := [indices(ExtShape, 'nolist')];
            w, e1 := do_gets(ixs, true, e) [];
            if not ('no_simpl' in {_rest}) then
                w := simpl_shape(w);
            end if;
            [ w, e1 ];
        end proc;

        local do_get := proc(f, f_ty, e, $)
            local sub, inds, rest;
            if e::`*` then
              sub := map(x->do_get(f, f_ty,x), [op(e)]);
              [ `And`(op(map2(op,1,sub))), `*`(op(map2(op,2,sub))) ]
            elif e::`^` then
              inds, rest := do_get(f, f_ty, op(1,e)) [] ;
              [ inds, subsop(1=rest, e) ]
            elif e:: f_ty then
              f(e)
            else
              [ true, e ]
            end if
        end proc;

        # apply a list of extractors, in order, until all fail to produce
        # any output .
        local do_gets := proc(todo::list, w, e, $)
            local t0, ts, w1, e1;
            if nops(todo) = 0 then
                [ w, e ]
            else
                t0 := op(1, todo);
                ts := op(subsop(1=NULL, todo));
                if indets(e, specfunc(t0)) <> {} then
                    w1, e1 :=
                      do_get(ExtShape[t0]:-MakeCtx
                            ,ExtShape[t0]:-MapleType
                            ,e) [] ;
                    ts := `if`(is(w1), [ts], [ts, t0]);
                    do_gets( ts, And(w1, w), e1 );
                else
                    do_gets( [ ts ], w, e );
                end if;
            end if;
        end proc;

        # todo: simplify the shape
        local simpl_shape := proc(e0,$)
            local e := Domain:-simpl_relation(e0);
            e := subsindets(e, specfunc(`Or`) , x->DSum(op(x)));
            e := subsindets(e, specfunc(`And`), x->DConstrain(op(x)));
            e;
        end proc;
    end module;
end module;
