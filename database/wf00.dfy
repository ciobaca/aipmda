method asdf(x : int, y : int)
  ensures {:ipm} x / y != 10              // protectWF(y != 0)
{
}

/*
method asdf(x : int, y : int)
  ensures {:ipm_wf} protect(x, "x") / protect(y, "y") != 10              // protectWF(y != 0)
{
}
*/

//
// x / y != 10              y != 0

// assert protectToProve(protect(y, "y") != 0, "y != 0", [x, y], true)

// assert protectToProve(x / y != 10, "x / y != 10", [x, y], false)


// protectToProve(x / y != 10, "", true, [ y != 0 ])

/*
   WF condition:

   Expression wellFormedness(Expression e)
   {
     ....
   }

   protectToProve(wellFormedness(e), true) daca e are atributul "ipm_wf"

   protectToProve(wellFormedness(e)) daca e are atributul "ipm_wf"


   ...
   protectToProve(y != 0, true)
   ...
   
   
   */