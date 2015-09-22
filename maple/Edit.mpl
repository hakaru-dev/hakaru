go := module ()
  local undoStack, sr;
  export here, where, up, child, fac, trm, silent, undo, ModuleApply;

  where := [];

  up := proc()
    here, where := op(1,where)(here),
                   [op(2..-1,where)];
  end proc;

  child := proc(i :: integer)
    local _;
    here, where := op(i,here),
                   [unapply(subsop(i=_,here), _), op(where)];
  end proc;

  sr := proc(operator, t :: type)
    local s, r, _;
    if here :: operator then
      s, r := selectremove(type, here, t);
      here, where := s, [unapply(operator(_,r), _), op(where)];
    elif type(here, t) then
      where := [(_->_), op(where)];
    else
      here, where := operator(), [unapply(operator(_,here), _), op(where)];
    end if
  end proc;

  silent := proc()
    local instr, _, j;
    for instr in _passed do
      if instr :: list then
        thisproc(op(instr))
      elif instr :: integer then
        child(instr)
      elif instr = up then
        up()
      elif instr :: all(anything) then
        here, where := op(1,instr),
                       [unapply(subsindets(here,identical(op(1,instr)),(x->_)),
                                _),
                        op(where)];
      elif instr :: fac(type) then
        sr(`*`, op(1,instr))
      elif instr :: trm(type) then
        sr(`+`, op(1,instr))
      elif instr :: type then
        j := [seq(`if`(op(j,here) :: instr, j, NULL), j=1..nops(here))];
        if nops(j) = 1 then
          child(op(1,j))
        else
          error "not unique: %%", op(map(op, j, here))
        end if
      elif instr :: procedure then
        here := instr(here)
      end if
    end do
  end proc;

  undoStack := [];

  undo := proc()
    here, where := op(op(1,undoStack));
    undoStack := [op(2..-1,undoStack)]:
    here, where;
  end proc;

  ModuleApply := proc()
    undoStack := [[here, where], op(undoStack)];
    try silent(_passed);
    finally print(here, where);
    end
  end proc;
end module:
