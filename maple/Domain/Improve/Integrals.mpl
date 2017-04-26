redundant_DIntos := module()
  export ModuleApply := proc(vs :: DomBound, sh :: DomShape, $)
    # This 'simplification' removes redundant information, but it is
    # entirely pointless as the result should be the same anyways. This
    # is mainly here as an assertion that Apply properly
    # re-applies integrals when the domain shape does not explicitly
    # state them.
    subsindets( sh, DomInto
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
  end proc;

  export SimplName  := "Obviously redundant 'DInto's";
  export SimplOrder := 2;
end module;


empty_DIntos := module()
  uses Domain;

  export ModuleApply := proc(vs,sh,$)
    subsindets(sh, satisfies(is_empty), _->DSum());
  end proc;

  local is_empty := proc(e,$)
    evalb(e = DSum()) or (evalb(op(0,e) = DInto) and is_empty(op(3,e)));
  end proc;

  export SimplName  := "Empty DIntos";
  export SimplOrder := 15;
end module;
