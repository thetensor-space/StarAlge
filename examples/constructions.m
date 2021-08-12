/* 
    Copyright 2013--2017, Peter A. Brooksbank, James B. Wilson.
    Distributed under GNU GPLv3.
*/



   /*---
   This file is not a part of the package. It contains functions
   useful for testing the code. In particular there are functions
   for building random systems of forms. There are also functions
   that can be used to build systems whose isometry group has a 
   prescribed structure.
   ---*/
   
import "form.m": StandardReflexiveForm;


SystemOfFormsToBilinearMap := function (S)
     K := Parent (S[1][1][1]);
     n := Nrows (S[1]);
return [ [ Vector (K, [S[t][i][j] : t in [1..#S]]) :
               j in [1..n] ] : i in [1..n] ];
end function;


BilinearMapToSystemOfForms := function (BM) 
     dimU := #BM; 
     dimV := #BM[1]; 
     dimW := Degree (BM[1][1]);
     K := BaseRing (BM[1][1]);
     MA := [];
     if dimU eq dimV then 
        MA := MatrixAlgebra (K, dimU);
     else
        MA := RMatrixSpace (K, dimU, dimV);
     end if;
     mats := [ [ [ BM[i][j][k] : j in [1..dimU] ] : 
                   i in [1..dimV] ] : k in [1..dimW] ];
     sigma := [ MA!(Matrix (X)) : X in mats ];
return sigma;    
end function;


IsAlternatingBilinearMap := function (BM)
     if ( #BM ne #BM[1] ) then
         return false;
     end if;
     for i in [1..#BM] do
         for j in [i..#BM] do
            if ( BM[i][j] ne -BM[j][i] ) then
               return false;
            end if;
         end for;
     end for;
return true;
end function;


IsSymmetricBilinearMap := function (BM)
     if ( #BM ne #BM[1] ) then
         return false;
     end if;  
     for i in [1..#BM] do
         for j in [i..#BM] do
            if ( BM[i][j] ne BM[j][i] ) then
               return false;
            end if;
         end for;
     end for;
return true;
end function;


scalar_times_BM := function (alpha, BM)
return [ [ alpha * BM[i][j] : j in [1..#BM[1]] ] : i in [1..#BM] ];
end function;


matrix_times_BM := function (A, BM)
     system := BilinearMapToSystemOfForms (BM);
return SystemOfFormsToBilinearMap ([ A * system[i] : 
                        i in [1..#system] ]);
end function;


BM_times_matrix := function (BM, A)
     system := BilinearMapToSystemOfForms (BM);
return SystemOfFormsToBilinearMap ([ system[i] * A : i in [1..#system] ]);
end function;


PreservesBilinearMap := function (G, BM)
     system := BilinearMapToSystemOfForms (BM);
return forall { i : i in [1..#system] |
           forall {j : j in [1..Ngens (G)] |
               G.j * system[i] * Transpose (G.j) eq system[i]} };
end function;
 

RandomConjugateOfBilinearMap := function (BM)
     n := #BM;
     F := BaseRing (BM[1][1]);
     x := Random (GL (n, F));
return matrix_times_BM (x, BM_times_matrix (BM, Transpose (x)));
end function;


DirectSumOfBilinearMaps := function (BM1, BM2)
     m1 := #BM1;
     assert m1 eq #BM1[1];
     m2 := #BM2;
     assert m2 eq #BM2[1];
     W1 := Parent (BM1[1][1]);
     W2 := Parent (BM2[1][1]);
     W := VectorSpace (BaseRing (W1), Degree (W1) + Degree (W2));
     // initialise <BM>
     BM := [ [ W!0 : a in [1..m1+m2] ] : b in [1..m1+m2] ];
     for i in [1..m1] do
         for j in [1..m1] do
            BM[i][j] := W!(Eltseq (BM1[i][j]) cat Eltseq (W2!0));
         end for;
     end for;
     for i in [1..m2] do
         for j in [1..m2] do
            BM[m1+i][m1+j] := W!(Eltseq (W1!0) cat Eltseq (BM2[i][j]));
         end for;
     end for;
return BM;
end function;


TensorProductOfBilinearMaps := function (BM1, BM2)
     m1 := #BM1;
     assert m1 eq #BM1[1];
     m2 := #BM2;
     assert m2 eq #BM2[1];
     W1 := Parent (BM1[1][1]);
     W2 := Parent (BM2[1][1]);
     W := TensorProduct (W1, W2);
     // initialise <BM>
     BM := [ [ W!0 : a in [1..m1*m2] ] : b in [1..m1*m2] ];
     for i in [1..m1] do  
     // modify all m2 x m2 blocks on level i 
        for j in [1..m1] do 
        // modify the (i,j)-th m2 x m2 block
           for k in [1..m2] do
              for l in [1..m2] do
    	         BM[(i-1)*m2+k][(j-1)*m2+l] := 
                       TensorProduct (BM1[i][j], BM2[k][l]);
	      end for;
           end for;
        end for;    
     end for;
return BM;
end function;


/*
  Given: 
    BM     :  a K-bilinear map b:U x V --> W,
    theta  :  an involution in GL(W); this may be input 
              as a matrix or scalar in K.

  Return: the theta-quasi-symmetric bilinear map 
          c:(U x V) x (U x V) --> W defined by 
          c((u,v),(u',v')) = b(u,v')+b(u',v)theta.

   Warning:  this function does not verify the inputs are correct
   and its behavior is not defined for faulty inputs.

   See also
       direct_sum_BM, tensor_product_BM
 */
crossed_map_BM := function (BM, theta)
     dimU := #BM; 
     dimV := #BM[1]; 
     dimW := Degree (BM[1][1]);
     K := BaseRing (BM[1][1]);
     forms1 := BilinearMapToSystemOfForms (BM);
     forms2 := BilinearMapToSystemOfForms ([[ BM[i][j]*theta : 
                            j in [1..dimV]]:i in [1..dimU]]);
     MA := MatrixAlgebra (BaseRing (BM[1][1]), dimU + dimV);
     CM:= [];
     for i in [1..#forms1] do
         c := Zero (MA); 
         InsertBlock (~c, forms1[i], 1, dimU + 1);
         InsertBlock (~c, forms2[i], dimU + 1, 1);
         Append (~CM, c);
     end for;
return SystemOfFormsToBilinearMap (CM);
end function;


identity_BM := function (F, n)
     V := VectorSpace (F, 1);
     BM := [ [ V!0 : i in [1..n] ] : j in [1..n] ];
     for k in [1..n] do
         BM[k][k] := V.1;
     end for;
return BM;
end function;


    /* functions that construct certain special bilinear maps */

__pad := function (list, V)
    v := Zero (V);
    for i in [1..#list] do
        v[i] := list[i];
     end for;
return v;
end function;


/*  
  Given:   
    poly --  the polynomial a(x) = a_0*x^0 + ... + a_d*x^d as input by
             the coefficient sequence [a_0 ... a_d], by default a(x)=0.         
    e --     the truncation parameter; this must be at most deg a(x). 
             Furthermore, if deg a(x)>1 then e must be at least  2 
                                 (the default).
  Return: 
      a bilinear map b:K^d x K^d --> K^e  where 
      Adj(b) = ( K[x]/(a(x)),  p(x)^* = p(x) )  
      represented on K^d by identifying x with the companion matrix 
      of a(x) (rather, the monic polynomial produced by scaling a(x)).
      By default the polynomial is trivial and so the return is simply
      multiplication in K.
*/
__polynomial_bilinear_map := function (K : poly := [0], e := 2)
    d := #poly - 1;
    if d le 1 then
        return SystemOfFormsToBilinearMap ([ Matrix (K, 1, 1, [1]) ]);
    end if;

    P<x> := PolynomialAlgebra (K);
    p :=  P!poly;
    I := ideal <P|[p]>;
    Q := P / I;  
    X := [ Q!x^i : i in [0..d-1] ];
    V := VectorSpace (K, d);
    W := VectorSpace (K, e);
    MW := MatrixAlgebra (K, e); 
    pi := Zero (RMatrixSpace (K, d, e));
    InsertBlock (~pi, Identity (MW), d+1-e, 1);
    BM := [ [(__pad (Eltseq (a*b), V)) * pi  : a in X ] : b in X ];

return BM;
end function;


__smallest_symmetric_rank1_orthogonal_type := function (K)
return SystemOfFormsToBilinearMap ([ Matrix (K, 1, 1, [1]) ]);
end function;


__smallest_alternating_rank1_orthogonal_type := function (K)
     MA := MatrixAlgebra (K, 3);
     X := MA![0,1,0,   -1,0,0,    0,0,0];
     Y := MA![0,0,1,    0,0,0,   -1,0,0];
     Z := MA![0,0,0,     0,0,1,   0,-1,0];
return SystemOfFormsToBilinearMap ([X, Y, Z ]);
end function;


__smallest_alternating_rank1_unitary_type := function (K)
     w := PrimitiveElement (K);
     MA := MatrixAlgebra (K, 6);
     Q := MA!0;
     X := Q; Y := Q; Z := Q; W := Q;
     X[1][2] := 1; X[2][1] := -1; X[4][5] := -w; X[5][4] := w;
     Y[1][3] := 1; Y[3][1] := -1; Y[4][6] := -w; Y[6][4] := w;
     Z[2][3] := 1; Z[3][2] := -1; Z[5][6] := -w; Z[6][5] := w;
     W[1][4] := 1; W[4][1] := -1;
return SystemOfFormsToBilinearMap ([ X, Y, Z, W ]);
end function;


__smallest_Hermitian_rank1_unitary_type := function (K)
     w := PrimitiveElement (K);
     MA := MatrixAlgebra (K, 2);
     X := MA![1,0,0,1];
     Y := MA!0;
     Y[1][2] := 1;
     Y[2][1] := w;
return SystemOfFormsToBilinearMap ([X, Y]);
end function;


__smallest_alternating_radfree_exchange_type := function (K)
     MA := MatrixAlgebra (K, 4);
     X := MA![0,0,1,0,  0,0,0,0,  -1,0,0,0,  0,0,0,0];
     Y := MA![0,0,0,1,  0,0,0,0,  0,0,0,0,  -1,0,0,0];
     Z := MA![0,0,0,0,  0,0,1,0,  0,-1,0,0,  0,0,0,0];
     W := MA![0,0,0,0,  0,0,0,1,  0,0,0,0,  0,-1,0,0];
return SystemOfFormsToBilinearMap ([X, Y, Z, W]);
end function;


__smallest_symmetric_radfree_exchange_type := function (K)
     MA := MatrixAlgebra (K, 4);
     X := MA![0,0,1,0,  0,0,0,0,  1,0,0,0,  0,0,0,0];
     Y := MA![0,0,0,1,  0,0,0,0,  0,0,0,0,  1,0,0,0];
     Z := MA![0,0,0,0,  0,0,1,0,  0,1,0,0,  0,0,0,0];
     W := MA![0,0,0,0,  0,0,0,1,  0,0,0,0,  0,1,0,0];
return SystemOfFormsToBilinearMap ([X, Y, Z, W]);
end function;


__smallest_exchange_exchange_type := function (K)
     MA := MatrixAlgebra (K, 2);
     X := MA![0,1,  0,0];
     Y := MA![0,0,  1,0];
return SystemOfFormsToBilinearMap ([X, Y]);
end function;


__increase_rank := function (BM, rank)
     I := identity_BM (BaseRing (BM[1][1]), rank);
     BM := TensorProductOfBilinearMaps (I, BM);
return BM;
end function;



/* ---- begin: names ---- */
SYMMETRIC := "1";
ALTERNATING := "-1";
HERMITIAN := "H";
EXCHANGE := "X";
/* ---- end: names ---- */


OrthogonalTypeBilinearMap := function (K, r : theta := SYMMETRIC, 
                                              poly := [1], 
                                              e := 2
                                      ) 
     case theta :
         when ALTERNATING :
            rank1_map := __smallest_alternating_rank1_orthogonal_type (K);
         when SYMMETRIC :
            rank1_map := __smallest_symmetric_rank1_orthogonal_type (K);
     else :
         "quasi-symmetric type not supported, defaulting to 
            symmetric.";
          rank1_map := __smallest_symmetric_rank1_orthogonal_type (K);
     end case;     
     poly_map := __polynomial_bilinear_map (K : poly := poly, e := e);   
     rank1_poly_map := TensorProductOfBilinearMaps (rank1_map, poly_map);       return __increase_rank (rank1_poly_map, r);
end function;


/* 
PAB: 03/09/2011
this function does not give the correct output 
*/
UnitaryTypeBilinearMap := function (K, r : theta := HERMITIAN, 
                                           poly := [1], 
                                           e := 2 
                                   )         
     case theta :
         when ALTERNATING :
            rank1_map := __smallest_alternating_rank1_unitary_type (K);
         when HERMITIAN :
            rank1_map := __smallest_Hermitian_rank1_unitary_type (K);
     else :
         "quasi-symmetric type not supported, defaulting to 
            Hermitian.";
         rank1_map := __smallest_alternating_rank1_unitary_type (K);
     end case; 
     poly_map := __polynomial_bilinear_map (K : poly := poly, e := e);
     rank1_poly_map := TensorProductOfBilinearMaps (rank1_map, poly_map);
return __increase_rank (rank1_poly_map, r);
end function;


ExchangeTypeBilinearMap := function (K, r : theta := EXCHANGE, 
                                            poly := [1], 
                                            e := 2
                                    ) 
     case theta:
         when SYMMETRIC :
              rank1_map := __smallest_symmetric_radfree_exchange_type (K);
         when ALTERNATING :
              rank1_map := __smallest_alternating_radfree_exchange_type (K);
         when EXCHANGE :
              rank1_map := __smallest_exchange_exchange_type (K);
         else :
              "quasi-symmetric type not supported, defaulting to exchange";
              rank1_map := __smallest_exchange_exchange_type (K);
     end case;    
     poly_map := __polynomial_bilinear_map (K : poly := poly, e := e);
     rank1_poly_map := TensorProductOfBilinearMaps (rank1_map, poly_map);   
return __increase_rank (rank1_poly_map, r);
end function;


SymplecticTypeBilinearMap := function (K, r : poly := [1], e := 2 )
     rank1_poly_map := __polynomial_bilinear_map (K : poly := poly, e := e);
     B := __increase_rank (rank1_poly_map, r);
return crossed_map_BM (B, -1);
end function;


   /*--- finally some functions for constructing random examples ---*/



/*
  <d> is the degree of the common module and <k> is its
  base ring; <t> is the number of groups in the intersection.
*/

RandomListOfClassicalGroups := function (d, k, t)
     if Degree (k) mod 2 eq 1 then
         if d mod 2 eq 1 then
            options := [2];
         else
            options := [1,3,4];
         end if;
     else
         if d mod 2 eq 1 then
            options := [2,5];
         else
            options := [1,3,4,5];
         end if;
     end if;
     groups := [ ];
     for i in [1..t] do
         s := Random (options);
         if s eq 1 then
            G := RandomConjugate (Sp (d, k));
         elif s eq 2 then
            G := RandomConjugate (GO (d, k));
         elif s eq 3 then
            G := RandomConjugate (GOPlus (d, k));
         elif s eq 4 then
            G := RandomConjugate (GOMinus (d, k));
         else
            G := RandomConjugate (GU (d, k));
         end if;
         Append (~groups, G);
     end for;
return groups;
end function;


/*
  <d> is the degree of the common module and <k> is its base ring;
  <r> is the dimension of the common radical of the forms;
  <ranks> is the list of ranks of the forms in the system.
*/

RandomSystemOfForms := function (d, k, r, ranks)
     if d lt (r + Max (ranks)) then
         return [], [];
     end if;
     MAd := MatrixAlgebra (k, d);
     n := d - r;
     MAn := MatrixAlgebra (k, n);
     Forms := [ ];
     Autos := [ ];
     Signs := [ ];
     for i in [1..#ranks] do
         m := ranks[i];
         if Degree (k) mod 2 eq 1 then
            if m mod 2 eq 1 then
               options := [2];
            else
               options := [1,3,4];
            end if;
         else
            if m mod 2 eq 1 then
               options := [2,5];
            else
               options := [1,3,4,5];
            end if;
         end if;
         s := Random (options); 
         if s eq 1 then
            F := StandardReflexiveForm ("symplectic", m, k);
            e := 0;
            sgn := -1;
         elif s eq 2 then
            F := StandardReflexiveForm ("orthogonalcircle", m, k);
            e := 0;
            sgn := 1;
         elif s eq 3 then
            F := StandardReflexiveForm ("orthogonalplus", m, k);
            e := 0;
            sgn := 1;
         elif s eq 4 then
            F := StandardReflexiveForm ("orthogonalminus", m, k);
            e := 0;
            sgn := 1;
         else
            F := StandardReflexiveForm ("unitary", m, k);
            e := Degree (k) div 2;
            sgn := 1;
         end if;
         F := InsertBlock (MAn!0, F, 1, 1);
         g := Random (GL (n, k));
         F := FrobeniusImage (g, e) * F * Transpose (g);
         F := InsertBlock (MAd!0, F, 1, 1);
         Append (~Forms, F);
         Append (~Autos, e);
         Append (~Signs, sgn);
     end for;
     x := Random (GL (d, k));
     Forms := [ 
          FrobeniusImage (x, Autos[i]) * Forms[i] * Transpose (x) :
              i in [1..#Forms] 
              ];
assert forall { i : i in [1..#Forms] | 
    Transpose (Forms[i]) eq Signs[i] * FrobeniusImage (Forms[i], Autos[i]) };
return Forms, Autos;
end function;

/*
  Added by PAB on 8/23/2021 to provide a source of examples 
  of *-algebras in characteristic 2 having non-trivial radicals
*/
RandomStarAlgebraWithRadical := function (d, e)
  q := 2^e;
  G1 := Sp (d, q);
  F1 := ClassicalForms (G1)`bilinearForm;
  found := false;
  count := 0;
  LIMIT := 1000;
  while count lt LIMIT and not found do
    G2 := RandomConjugate (G1);
    F2 := ClassicalForms (G2)`bilinearForm;
    A := AdjointAlgebra ([F1, F2]);
    J := JacobsonRadical (A);
if (Dimension (J) gt 0) and (Dimension (J*J) gt 0) then    // try to get higher class
      found := true;
end if;
  end while;
  if found then 
    return A;
  else
    "failed to find an example after", LIMIT, "tries";
    return false;
  end if;
end function;

// this is the example from the paper; bit of a hack
__star_image := function (M, t, one)
  N := M;
  InsertBlock (~N, (one + t) * ExtractBlock (M, 1, 3, 2, 2), 3, 1);
  InsertBlock (~N, (one + t) * ExtractBlock (M, 3, 1, 2, 2), 1, 3);
return N;
end function;

Example10 := function (e)
  K := GF (2^e);
  ma := MatrixAlgebra (K, 2);
    // make truncated poly algebra as algebra of 2 x 2 matrices
  t := ma![0,1,0,0];
  one := Identity (ma);
    // build 2 x 2 matrix algebra over this ring
  MA := MatrixAlgebra (K, 4);
  z := MA!0;
  A := sub < MA | 
             [
             InsertBlock (z, t, 1, 1),
             InsertBlock (z, one, 1, 1),
             InsertBlock (z, t, 1, 3),
             InsertBlock (z, one, 1, 3),
             InsertBlock (z, t, 3, 1),
             InsertBlock (z, one, 3, 1),
             InsertBlock (z, t, 3, 3),
             InsertBlock (z, one, 3, 3)
             ]
           >;
  star := hom < A -> A | M :-> __star_image (M, t, one) >;
  A`Star := star;
return A;
end function;