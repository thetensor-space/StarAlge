/* 
  Created by PAB on 7/23/2021.

  Implementation of algorithms for isometry tests in the characteristic 2 case.
*/


// RadicalUnitarians will be a subroutine once it's been adequately tested.

__trace := function (A, z) return z + z @ A`Star; end function;

__norm := function (A, z) return (z @ A`Star) * z; end function;

__delta := function (A, z) return __trace (A, z) + __norm (A, z); end function;

intrinsic RadicalUnitarians (A::AlgMat) -> GrpMat

  { Return the subgroup of A^# lying within 1 + J(A). }

  d := Degree (A);
  F := BaseRing (A);
  one := Identity (A);

  J := JacobsonRadical (A);
  
  G := sub < GL (d, F) | [ one + J.i : i in [1..Ngens (J)] ] >;
  // refine G through the layers of the radical
  K := J;
  while Dimension (K) gt 0 do
  
    U := J * K;
    
    // build matrix representing F-linear map <mu> : G / [G,G] ---> K / U
    W, pi := quo < K | U >;
    M := Matrix ([ __delta (A, A!(G.i) - one) @ pi : i in [1..Ngens (G)] ]);
    
    // calculate the nullspace and pull back into G
    null := Nullspace (M);
       /* <<PAB: only works for GF(2) right now>> */
    ker := sub < G | [
            &* [ G.i^Integers ()!(n[i]) : i in [1..Ngens (G)] ] : n in Basis (null)
                     ]
                >;
                
    // reassign G and K
    K := U;
    G := sub < G | ker , DerivedSubgroup (G) >;
    
  end while;
  
assert forall { i : i in [1..Ngens (G)] | G.i @ A`Star * G.i eq Identity (G) };

return G;

end intrinsic;



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
  

