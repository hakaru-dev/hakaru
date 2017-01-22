# Wrapper for existing Hakaru test functions,
# to make the output a bit nicer and to (potentially?)
# only collect information about tests without running them
# This is hard because some tests throw Maple errors...
TestWrapper := module ()
  option package;
  export ModuleApply, RunTest, PrintTest, MakeTest
       , RunOpts;
  local TestGroups, ModuleLoad;

  # Only works if numArgs is less than 4...
  PrintTest :=
    proc (testGroup :: string)
    local numArgs;
    numArgs := TestGroups[testGroup]['numArgs'];

    proc (a0::uneval,a1::uneval,a2::uneval,a3::uneval)
      op(0..numArgs+1,[_passed]);
    end proc;
  end proc;

  # Runs a test in a group..
  RunTest := proc
    ( testGroup :: string, lbl :: string
    )
    proc ()
      local testixl, res, testProc;
      if RunOpts['DoRun'] then
        testProc := TestGroups[testGroup]['runTest'];
        testixl := nops([indices(TestGroups[testGroup]['tests'])]);

        printf("===BEGIN(%s:%d) %s===\n", testGroup, testixl, lbl);
        res := "SUCCESS";

        try testProc(_passed)
        catch:
          printf("%s\n",
              StringTools:-FormatMessage(lastexception[2 .. -1])
              );
          res := "ERROR";
        finally
          printf("===END(%s:%d) %s ===\n\n", testGroup, testixl, res);
        end try ;

      end if;
    end proc;
  end proc;

  MakeTest := proc
   ( testProc
   , {testGroup :: string := "(Maple)"}
   , {testArgs :: Or('0',posint) := 2}
   , $
   )
     # Create the test group if needed
     if not assigned(TestGroups[testGroup]) then
        TestGroups[testGroup]['tests'];
        TestGroups[testGroup]['numArgs'] := testArgs;
        TestGroups[testGroup]['runTest'] := testProc;
     end if;

     proc()
        local lbl;

        # Find the test label
        lbl :=
          op([1,2],select(type, [_passed], `=`(identical('label'),'anything')));

        # Print the test and store it
        TestGroups[testGroup]['tests'][lbl] :=
           PrintTest(testGroup)(_passed);

        # Run the test
        RunTest(testGroup,lbl)(_passed);

     end proc;
  end proc;

  ModuleLoad := proc($)
     RunOpts['DoRun'] := true;
  end proc;

  # Loads the given module with the given options
  ModuleApply := proc(fn::'string', {runOpts:=[]}
    )
     # Setup options
     if not is(runOpts,[]) then RunOpts := runOpts; end if;

     # Read a file containing some tests
     read(fn);

  end proc;

  ModuleLoad();
end module;
