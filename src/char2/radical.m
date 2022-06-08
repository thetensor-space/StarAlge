/* 
 * Created by PAB on 7/23/2021. 
 * Modified by PAB on 4/29/2022.
*/

import "util.m" : StarDelta;


/*
 * Given a *-algebra, A, find the subgroup of the unitarian 
 * group A^# that lies in 1 + J(A). This method replaces the
 * power series trick used in the odd characteristic case.
 *
 * Note: in a future code overhaul there should be a single 
 * intrinsic that applies to *-algebras in all characteristics.
*/
intrinsic RadicalUnitarians (A::AlgMat) -> GrpMat

  { Return the subgroup of A^# lying within 1 + J(A). }

  d := Degree (A);
  F := BaseRing (A);
  f := Degree (F);
  rho := PrimitiveElement (F);
  one := Identity (A);

  J := JacobsonRadical (A);

// fix the general field case
  gens := &cat [ [ one + rho^j * J.i : j in [0..f-1] ] : i in [1..Ngens (J)] ];
  G := sub < GL (d, F) | gens >;
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




