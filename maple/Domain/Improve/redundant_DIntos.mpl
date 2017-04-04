local redundant_DIntos := proc(dom, $)
    local vs, sh;
    vs, sh := op(dom);
    # This 'simplification' removes redundant information, but it is
    # entirely pointless as the result should be the same anyways. This
    # is mainly here as an assertion that Apply properly
    # re-applies integrals when the domain shape does not explicitly
    # state them.
    sh := subsindets( sh, DomInto
                    , proc (x, $)
                          local x_vn, x_t0, x_rest, x_t, x_mk;
                          x_vn, x_t0, x_rest := op(x);
                          x_t, x_mk := Domain:-Bound:-get(vs, x_vn);
                          if x_t = x_t0 then
                              x_rest
                          else
                              x
                          end if;
                     end proc );
    DOMAIN(vs, sh);
end proc;

