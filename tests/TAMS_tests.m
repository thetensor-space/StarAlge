

   /*--- 
   Here are some sample test functions for building
   systems of forms having isometry groups with
   prescribed structure.

   These are in fact the constructions used in:

   P.A. Brooksbank and J.B. Wilson, Computing isometry
   groups of hermitian maps, to appear in TAMS.
   ---*/


/*
   Build some examples that have semisimple structure
   
   O(2,5) \oplus U(3,5)
   
   and have a radical of nilpotence degree 7.
   
   These examples are used, among other things, to
   illustrate the power series technique to compute
   the unipotent radical; notice that the nilpotence
   degree exceeds the characteristic, so usual
   exponentiation of nilpotent elements will not work.
*/

TAMS_test1 := function (runs)
     times := [ ];
     for i in [1..runs] do
"test 1. run ", i;	
	 BMO := OrthogonalTypeBilinearMap (GF (5), 2 : 
                   theta := ALTERNATING, poly := [0,0,0,0,0,0,0,1] );
	 BMU := UnitaryTypeBilinearMap (GF (5), 3 : 
                   theta := ALTERNATING, poly := [0,0,1] );
	 BMOr := RandomConjugateOfBilinearMap (BMO);
	 BMUr := RandomConjugateOfBilinearMap (BMU);
	 BMtest1 := DirectSumOfBilinearMaps (BMOr, BMUr);
	 BMtest1r := RandomConjugateOfBilinearMap (BMtest1);	
         Forms := BilinearMapToSystemOfForms (BMtest1r);
	 t := Cputime ();
	 isom_test1 := IsometryGroup (Forms);
	 Append (~times, Cputime (t));
"time: ", times[i];
     end for;
return times;
end function;


/*
   A similar sort of example. This time the prescribed structure is
   
   Sp(4,9) \oplus X(4,9)
   
   with a radical of nilpotence degree 5. Once again, observe that
   the nilpotence degree exceeds the characteristic.
*/

TAMS_test2 := function (runs)
     times := [ ];
     for i in [1..runs] do
"test 2, run ", i;	
         BMSp := SymplecticTypeBilinearMap (GF(9), 2 : poly := [0,0,0,0,1]);
	 BMX := ExchangeTypeBilinearMap (GF(9), 4 : theta := ALTERNATING);
	 BMSpr := RandomConjugateOfBilinearMap (BMSp);
	 BMXr := RandomConjugateOfBilinearMap (BMX);
	 BMtest2 := DirectSumOfBilinearMaps (BMSpr, BMXr);
	 BMtest2r := RandomConjugateOfBilinearMap (BMtest2);
         Forms := BilinearMapToSystemOfForms (BMtest2r);
  	 t := Cputime ();
	 isom_test2 := IsometryGroup (Forms);
	 Append (~times, Cputime (t));
"time: ", times[i];
     end for;
return times;
end function;


