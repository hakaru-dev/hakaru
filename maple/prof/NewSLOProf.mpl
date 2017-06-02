NewSLO:-Profile(
  proc()
    writeto(`if`(StringTools[Has](kernelopts(system), "Windows"), "NUL", "/dev/null"));
    read("NewSLOTests.mpl");
    writeto(terminal);
  end proc,
  {_prof_name="NewSLO"});
