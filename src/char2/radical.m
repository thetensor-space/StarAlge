/* 
  Created by PAB on 7/23/2021.

  Implementation of algorithms for isometry tests in the characteristic 2 case.
*/

import "util.m" : StarDelta;



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
    M := Matrix ([ StarDelta (A, A!(G.i) - one) @ pi : i in [1..Ngens (G)] ]);
    
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




