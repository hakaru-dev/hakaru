# Wrapper for existing Hakaru test functions,
# to make the output a bit nicer and to (potentially?)
# only collect information about tests without running them
# This is hard because some tests throw Maple errors...
TestWrapper := module ()
  option package;
  export ModuleApply, RunTest, PrintTest, MakeTest
       , RunOpts, args_to_table;
  local TestGroups, ModuleLoad
      , BeginFmt, EndFmt ;

  # Only works if numArgs is less than 4...
  PrintTest :=
    proc (testGroup :: string)
    local numArgs;
    numArgs := TestGroups[testGroup]["numArgs"];

    proc (a0::uneval,a1::uneval,a2::uneval,a3::uneval)
      [op(1..numArgs,[_passed])];
    end proc;
  end proc;

  # Runs a test in a group..
  RunTest := proc
    ( testGroup :: string, lbl :: string
    )
    proc ()
      local testixl, res, testProc;
      if RunOpts["DoRun"] then
        testProc := TestGroups[testGroup]["runTest"];
        testixl := nops([indices(TestGroups[testGroup]["tests"])]);

        printf(BeginFmt, testGroup, testixl, lbl);
        res := "SUCCESS";

        try testProc(_passed)
        catch:
          printf("%s\n",
              StringTools:-FormatMessage(lastexception[2 .. -1])
              );
          res := "ERROR";
        finally
          printf(EndFmt, testGroup, testixl, res);
        end try ;

      else
        # lprintf("Printing... %s %s \n", testGroup, lbl);

        # TestGroups[testGroup]["tests"][lbl]();

      end if;
    end proc;
  end proc;

  MakeTest := proc
   ( testProc
   , {testGroup :: string := "(Maple)"}
   , {testArgs :: Or(identical(0),posint) := 2}
   , $
   )
     # Create the test group if needed
     if not assigned(TestGroups[testGroup]) then
        TestGroups[testGroup]["tests"];
        TestGroups[testGroup]["numArgs"] := testArgs;
        TestGroups[testGroup]["runTest"] := testProc;
     end if;

     proc()
        local lbl;

        # Find the test label
        lbl :=
          op([1,2],select(type, [_passed], `=`(identical('label'),'anything')));

        # Print the test and store it
        TestGroups[testGroup]["tests"][lbl] :=
           PrintTest(testGroup)(_passed);

        # Run the test
        RunTest(testGroup,lbl)(_passed);

     end proc;
  end proc;

  ModuleLoad := proc($)
     RunOpts["DoRun"] := true;
     BeginFmt := "";
     EndFmt   := "";
  end proc;

  # converts args (as an list of s-expr) to a table, ignoring things not of the form
  #   name = anything
  args_to_table := proc(as)
      local t;
      t :=
        map(q -> subsop(1=sprintf(op(1,q)),q),
          select(type,as, `=`({name, string},anything))
           );
      t := convert(t,table);
      return t;
  end proc;

  # Loads the given module with the given options
  ModuleApply := proc(fn:: string, runOpts:=[]
    )
     # Setup options
     if not is(runOpts,[]) then
         unprotect(`RunOpts`);
         TestWrapper:-RunOpts := args_to_table(runOpts);
         protect(`RunOpts`);
     end if;

     # Read a file containing some tests
     read(fn);

  end proc;

  ModuleLoad();
end module;
