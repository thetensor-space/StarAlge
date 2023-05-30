/*
 * Created on 4/29/2022 by PAB
*/

/* Represents A/J on J/J^2 but it may not be a faithful representation. */

__SQ_image := function (a, MA, W, f)
return MA!Matrix ([ (a * (W.i @@ f)) @ f : i in [1..Dimension (W)] ]);
end function;

__SQ_preimage := function (s, S, COB, gens)
  c := Vector (Coordinates (S, s)) * COB;
return &+ [ c[i] * gens[i] : i in [1..#gens] ];
end function;



intrinsic SemisimpleQuotient (A::AlgMat) -> AlgMat , Map , Map

{ Construct a matrix representation for the *-algebra A/J on J/J^2. }

  J := JacobsonRadical (A);
  F := BaseRing (A);
  
  if Dimension (J) eq 0 then 
      return A; 
  end if;

  // build quotient A/J as associative algebra to lift a basis for it
  B, g := quo < A | J >;
  gens := [ b @@ g : b in Basis (B) ];
  
  // build the faithful action of A/J on J/J^2
  W, f := quo < J | J*J >;
  MA := MatrixAlgebra (F, Dimension (W));
  induced_gens := [ __SQ_image (gens[i], MA, W, f) : i in [1..#gens] ];
  S := sub < MA | induced_gens >;
  assert Dimension (S) eq #gens;
  AtoS := hom < A -> S | a :-> __SQ_image (a, MA, W, f) >;
  
  // build lift from S to A
  COB := Matrix ([ Coordinates (S, induced_gens[i]) : i in [1..#induced_gens] ])^-1;
  StoA := hom < S -> A | s :-> __SQ_preimage (s, S, COB, gens) >;
  
  // define * on S
  S`Star := hom < S -> S | s :-> ((s @ StoA) @ A`Star) @ AtoS >;
  
return S, AtoS, StoA;

end intrinsic;
