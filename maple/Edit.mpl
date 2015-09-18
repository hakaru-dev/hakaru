go := module ()
  export here, where, up, silent, ModuleApply;

  up := proc() silent(up) end proc;

  silent := proc()
    local i, _;
    for i in _passed do
      if i :: list then
        thisproc(op(i))
      elif i :: integer then
        here, where := op(i,here), [unapply(subsop(i=_,here), _), op(where)];
      elif i = up then
        here, where := op(1,where)(here), [op(2..-1,where)];
      elif i :: all(anything) then
        here, where := op(1,i), [unapply(subsindets(here,identical(op(1,i)),(x->_)), _), op(where)];
      elif i :: procedure then
        here := i(here)
      end if
    end do
  end proc;

  ModuleApply := proc()
    try silent(_passed);
    finally print(here, where);
    end
  end proc;
end module:
