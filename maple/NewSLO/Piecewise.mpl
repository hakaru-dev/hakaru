
    # eval_piecewise has the same calling convention as eval_factor.
    # It simplifies piecewise expressions.
    eval_piecewise := proc(e :: specfunc(piecewise),
                           kb :: t_kb, mode :: identical(`*`,`+`),
                           loops :: list([identical(product,Product,sum,Sum),
                                          name=range]),
                           $)
      local default, kbs, pieces, i, cond, inds, res, s, r, x, b, a;
      default := 0; # the catch-all "else" result
      kbs[1] := kb;
      for i from 1 by 2 to nops(e) do
        if i = nops(e) then
          default := op(i,e);
          pieces[i] := default;
        else
          # Simplify piecewise conditions using KB
          cond := op(i,e);
          # cond := eval_factor(cond, kbs[i], `+`, []);
          kbs[i+1] := assert(cond, kbs[i]);
              # This condition is false in context, so delete this piece
              # by not putting anything inside "pieces"
          if kbs[i+1] :: t_kb then
            # find all of the assertions in "kbs[i+1] - kbs[i]"
            cond := map(proc(cond::[identical(assert),anything], $)
                          op(2,cond)
                        end proc,
                        kb_subtract(kbs[i+1], kbs[i]));
            if nops(cond) = 0 then
              default := op(i+1,e);
              pieces[i] := default;
              break;
            else
              cond := `if`(nops(cond)=1, op(1,cond), And(op(cond)));
            end if;
          end if;
          # TODO: Extend KB interface to optimize for
          #       entails(kb,cond) := nops(kb_subtract(assert(cond,kb),kb))=0
          kbs[i+2] := assert(Not(cond), kbs[i]);
          if not(kb_entails(kbs[i], kbs[i+2])) then
            pieces[i] := cond;
            pieces[i+1] := op(i+1,e);
          else
            # This condition is false in context, so delete this piece
            # by not putting anything inside "pieces"
          end if
        end if
      end do;
      # Combine duplicate branches at end
      inds := [indices(pieces, 'nolist', 'indexorder')];
      for i in ListTools:-Reverse(select(type, inds, 'even')) do
        if Testzero(pieces[i]-default) then
          pieces[i  ] := evaln(pieces[i  ]);
          pieces[i-1] := evaln(pieces[i-1]);
        else
          break;
        end if
      end do;
      # Special processing for when the pieces are few
      res := [entries(pieces, 'nolist', 'indexorder')];
      if nops(res) <= 1 then
        return eval_factor(default, kb, mode, loops);
      end if;
      # Recursively process pieces
      inds := [indices(pieces, 'nolist', 'indexorder')];
      for i in inds do
        if i::even or i=op(-1,inds) then
          # only simplify if the piece is not default;
          # note that kbs[i] could be NotAKB(), but this is still valid
          if not Testzero(pieces[i] - default) then
            pieces[i] := eval_factor(pieces[i], kbs[i], mode, []);
          end if;
        end if;
      end do;
      res := piecewise(entries(pieces, 'nolist', 'indexorder'));
      for i in loops do res := op(1,i)(res, op(2,i)) end do;
      return res;
    end proc;
