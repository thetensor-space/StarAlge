/*
 * Created on 4/29/2022 by PAB.
 *
 * Functions that convert the problem of computing isometries of 
 * a systems of forms to computing unitarian elements of a *-algebra. 
 * Eventually there should be a single intrinsic that works in 
 * all characteristics for all possible systems of forms. 
*/


RandomQuadraticForm := function (K, d)
     assert d mod 2 eq 0;
     repeat
          Q := UpperTriangularMatrix ([ Random (K) : i in [1..d*(d+1) div 2] ]);
     until Rank (Q + Transpose (Q)) eq d;
return Q;
end function;

__QFTSA_dot := function (A, J)
return J^-1 * Transpose (A) * J;
end function;

__QFTSA_star := function (AB, J, X)
     d := Degree (Parent (J));
     A := ExtractBlock (AB, 1, 1, d, d);
     assert A eq ExtractBlock (AB, d+1, d+1, d, d);
     B := ExtractBlock (AB, 1, d+1, d, d);
     A := __QFTSA_dot (A, J);
     B := __QFTSA_dot (B, J) + X*A + A*X;
     AB_star := DiagonalJoin (A, A);
     InsertBlock (~AB_star, B, 1, d+1);
return AB_star;
end function;

QuadraticFormToStarAlgebra := function (Q)
     d := Degree (Parent (Q));
     K := BaseRing (Parent (Q));
     ma := MatrixAlgebra (K, d);
     MA := MatrixAlgebra (K, 2*d);
     gens := [ DiagonalJoin (A, A) : A in Basis (ma) ];
     gens cat:= [ InsertBlock (MA!0, B, 1, d+1) : B in Basis (ma) ];
     ALG := sub < MA | gens >;
     J := Q + Transpose (Q);
     X := J^-1 * Q;
     ALG`Star := hom < ALG -> ALG | AB :-> __QFTSA_star (AB, J, X) >;
return ALG;
end function;

// test
d := 6;
e := 2;
K := GF (2^e);
Q := RandomQuadraticForm (K, d);
J := Q + Transpose (Q);
// use Don Taylor's functions
VQ := QuadraticSpace (Q);
ORTH := IsometryGroup (VQ); 
   // adjust to be isometries in our action
ORTH := sub < Generic (ORTH) | [ Transpose (ORTH.i) : i in [1..Ngens (ORTH)] ] >;
VJ := SymplecticSpace (J);
ISOM := IsometryGroup (VJ);
   // adjust to be isometries in our action
ISOM := sub < Generic (ISOM) | [ Transpose (ISOM.i) : i in [1..Ngens (ISOM)] ] >;
assert ORTH subset ISOM;

ALG := QuadraticFormToStarAlgebra (Q);
gens := [ ];
for i in [1..Ngens (ORTH)] do
     A := ORTH.i;
     M := Transpose (A) * Q * A + Q;
     assert M eq Transpose(M) and forall { a : a in [1..d] | M[a][a] eq 0 };
     for a in [1..d-1] do
          for b in [a+1..d] do
               M[a][b] := 0;
          end for;
     end for;
     assert (Transpose (A) * Q * A + Q) eq (M + Transpose (M));
     B := (Transpose (A) * J)^-1 * M;
     AB := Generic (ALG)!DiagonalJoin (A, A);
     InsertBlock (~AB, B, 1, d+1);
     assert AB in ALG;
     assert AB @ ALG`Star * AB eq Identity (ALG);
     Append (~gens, AB);  
end for;
