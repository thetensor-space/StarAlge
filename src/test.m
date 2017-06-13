/* 
    Copyright 2013--2017, Peter A. Brooksbank, James B. Wilson.
    Distributed under GNU GPLv3.
*/


VectorToForm := function (v, d)
     V := Parent (v);
     k := BaseRing (V);
     MA := MatrixAlgebra (k, d);
     A := Zero (MA);
     next := 0;
     for i in [2..d] do
         for j in [1..i - 1] do
            next +:= 1;
            A[i][j] := v[next];
         end for;
     end for;
return A - Transpose (A);
end function;

p := 3;
k := GF (p);
d := 6;
G := GL (d, k);
EG := ExteriorSquare (G);
W := VectorSpace (k, Degree (EG));
repeat
   U := sub < W | [ Random (W) , Random (W) ] >;
   S := [ VectorToForm (U.i, d) : i in [1..Ngens (U)] ];
until Dimension (U) eq 2;

tt := Cputime ();
"computing stabiliser by brute force...";
RandomSchreier (EG);
stab_brute := Stabiliser (EG, U);
"...done in time", Cputime (tt);

tt := Cputime ();
"computing stabiliser by norm-star...";
ns := NormStar (S);
Ens := ExteriorSquare (ns);
Enst := sub < Generic (Ens) | [ Transpose (Ens.i) : i in [1..Ngens (Ens)] ] >;
RandomSchreier (Enst);
stab_ns := Stabiliser (Enst, U);
"...done in time", Cputime (tt);

"same result?", stab_ns eq stab_brute;
