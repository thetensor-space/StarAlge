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
intrinsic RadicalUnitarians (A::AlgMat : 
                               VERIFY := false,
                               RANDOM := true
                            ) -> GrpMat

  { Return the subgroup of A^# lying within 1 + J(A). }

  d := Degree (A);
  F := BaseRing (A); 
  // PAB : might as well have this function incorporate odd char as well
  require Characteristic (F) eq 2 : "method only applies in characteristic 2";
  f := Degree (F);
  rho := PrimitiveElement (F);
  one := Identity (A);

  // initialize
  J := JacobsonRadical (A);
  gens := &cat [ [ one + rho^j * J.i : j in [0..f-1] ] : i in [1..Ngens (J)] ];
  G := sub < GL (d, F) | gens >;
  K := J;
  
  // refine G through the layers of the radical
  depth := 0;
  while Dimension (K) gt 0 do
  
tt := Cputime ();
    if VERIFY then  // with verbose printing will show the evolution of G through layers
         vprint Isometry, 1 : "[RadUnit] layer of radical series =", depth;
         vprint Isometry, 1 : "[RadUnit] order of G =", LMGOrder (G);
    end if;
    depth +:= 1;
"time to compute order =", Cputime (tt);
   
tt := Cputime (); 
    U := J * K;
 
    // build matrix representing GF(2)-linear map <mu> : G / G^2 * [G,G] ---> K / U
    K2, f := WriteOverSmallerField (K, GF(2));
    U2 := sub < K2 | [ U.i @ f : i in [1..Ngens (U)] ] >; 
    W, pi := quo < K2 | U2 >;

    M := Matrix ([ (StarDelta (A, A!(G.i) - one) @ f) @ pi : i in [1..Ngens (G)] ]);
    null := Nullspace (M);
"time to construct M and null space =", Cputime (tt); 
 
tt := Cputime ();    
    ker := sub < Generic(G) | [
            &* [ G.i^Integers ()!(n[i]) : i in [1..Ngens (G)] ] : n in Basis (null)
                     ]
                >;
"time to construct pullback into G =", Cputime (tt);

tt := Cputime ();
    if RANDOM then
         DG := DerivedGroupMonteCarlo (G);
    else 
         DG := LMGDerivedGroup (G);
    end if;
"time to compute derived subgroup of G =", Cputime (tt);   

tt := Cputime (); 
    G := sub < Generic(G) | ker , DG , [ G.i^2 : i in [1..Ngens(G)] ] >;
    K := U;
"time to update G and K =", Cputime (tt);
    
  end while;
  
tt := Cputime ();  
assert forall { i : i in [1..Ngens (G)] | G.i @ A`Star * G.i eq Identity (G) };
"time to verify output =", Cputime (tt);

return G;

end intrinsic;




