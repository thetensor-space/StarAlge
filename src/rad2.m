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
  K := J;
  G := sub < GL (d, F) | [ one + J.i : i in [1..Ngens (J)] ] >;

  // approximate through the layers of the radical
  while Dimension (K) gt 0 do
  
  "|G| =", #G;
  "dim(K) =", Dimension (K);
  
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


// QuotientByRadical will also be a subroutine ...

__induced_image := function (a, MA, W, f)
return MA!Matrix ([ (a * (W.i @@ f)) @ f : i in [1..Dimension (W)] ]);
end function;

intrinsic QuotientByRadical (A::AlgMat) -> AlgMat

{ Form the matrix rep of the *-algebra A/J on J/J^2. }

  J := JacobsonRadical (A);
  F := BaseRing (A);
  
  if Dimension (J) eq 0 then return A; end if;
  
  W, f := quo < J | J*J >;
  m := Dimension (W);
  MA := MatrixAlgebra (F, m);
  
  gens := [ __induced_image (A.i, MA, W, f) : i in [1..Ngens (A)] ];
  AW := sub < MA | gens >;
  
//  pi , pi_inv := __build_homs (A, AW, gens);
//star_gens := [ __induced_image (A.i @ A`Star, MA, W, f) : i in [1..Ngens (A)] ];
  
//return AW, pi, pi_inv;

return AW;

end intrinsic;