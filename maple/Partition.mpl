#This module implements `Partition`---Hakaru's replacement for Maple's 
#endogenous and unwieldy `piecewise`.

#The outer data structure for a Partition is a function, just like it is for 
#piecewise.

Partition:= module()
local
   #The ModuleApply simply type-checks its arguments and returns the
   #Partition structure.
   ModuleApply:= proc(
      Pairs::set(
         record(
            cond::boolean &under (convert, boolean_operator),
            #Is that inclusive enough?
            val::t_Hakaru
            #Is that inclusive enough?
         )
      )
   )
     #There's no effective way to use unevaluated 'procname' or 'thismodule'
     #in a ModuleApply. 
     'Partition'(_passed)
  end proc
;
end module: 
