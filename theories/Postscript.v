(** * Postscript : More than Analysis  *)

(** 
    Sadly, this project is far from completion. The expected paradigme should 
    look like something follow: 
<<
              Theoretical            Bridge        Computable
              ===========------------======--------===================
Mechanization                          ??          
              analyse                  ??          analyse_s   <-----+
                                       ??                            |
              | (co)induction          ??          | (syntax)        |
              | Moore Family           ??          | induction       |
              | ((̂C, ̂R), ⊑)            ??          | (constraints)   |
                                       ??                            |
              existence of soln        ??          constraints       |
                                       ??                            |
              preservation of soln     ??          graph formulation |
                                       ??                            | 
                                       ??          graph solution ---+
              ===========------------======--------===================
Verification  Formal Proof                         QuickCheck 
>>

    The project has grown considerably large even though we barely implemented
    the theorems and specifications on theory side without proofs yet and  
    the functions to compute the acceptance of an analysis and constraint
    solving program.

    Based on what are not yet accomplished, there is a fairly number of issues
    to solve in the future. 
 
  *)
