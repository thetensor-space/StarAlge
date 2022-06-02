/* 
    Copyright 2013--2017, Peter A. Brooksbank, James B. Wilson.
    Distributed under GNU GPLv3.

    Edited by Peter A. Brooksbank (June 2022) to incorporate
    decompositions of *-algebras in characteristic 2. 
*/


     /*--- Carry out standard ring decompositions of algebras. ---*/ 

import "star.m": StarOnBasis; 

import "grpalg.m": GroupAlgebraAsMatrixStarAlgebra;

/*
  Functions for the standard Wedderburn decomposition of matrix 
  algebras were adapted from code provided by Willem de Graaf 
  designed for the more general setting of algebras defined via 
  structure constants. The resulting functions for matrix algebras
  are therefore unlikely to be optimal.

  Functions for Taft decompositions of algebras with involution
  were designed by Peter Brooksbank and James Wilson, and are 
  based closely on Taft's original paper. They use Wedderburn
  decompositions repeatedly.
*/ 
 

                /* ---- Wedderburn decompositions ---- */


/* 
  The main worker function
*/
__Refine_WC := function (X, J)

assert Dimension (J) eq Ngens (J);
     MA := Generic (J);
     F := BaseRing (MA);
     d := Degree (MA);
     MS := RMatrixSpace (F, d, d);
     
     /* find a basis of <J> relative to <J>^2 */
     JJ := J * J;
     l := Dimension (J) - Dimension (JJ);
     assert l gt 0;
     temp := sub < MS | Basis (JJ) >;
     Jbas := [ MS!x : x in Basis (J) ];
     bas := [];
     while #bas lt l do
         assert exists (i){ j : j in [1..#Jbas] | 
                                       not Jbas[j] in temp  };
         Append (~bas, Jbas[i]);
         temp := sub < MS | Basis (temp) cat [Jbas[i]] >;
         Remove (~Jbas, i);
     end while;
     Jbas := bas cat [MS!x : x in Basis (JJ)];
     MJ := RMatrixSpaceWithBasis (Jbas);

     /* next a nice basis of sp(<X>)<J> */
     bas := [MS!x : x in X] cat Jbas;
     MX := RMatrixSpaceWithBasis (bas);
     n := #X;
     
     /* store the necessary scalar arrays */
     beta := [ [ ] : i in [1..n] ];     // <n> x <n> with entries in F^n
     delta := [ [ ] : i in [1..n] ];    // <n> x <n> with entries in F^l
     for i in [1..n] do
         for j in [1..n] do
             c := Coordinates (MX, MX!(X[i] * X[j]));
             beta[i][j] := [ c[z] : z in [1..n] ];
             delta[i][j] := [ c[z] : z in [n+1..n+l] ];
         end for;
     end for;
   
     lambda := [ [ ] : i in [1..n] ];  
     mu := [ [ ] : i in [1..n] ];   //  both <n> x <l> with entries in F^l
     for i in [1..n] do
         for t in [1..l] do
             c := Coordinates (MJ, MJ!(Jbas[t] * X[i]));
             lambda[i][t] := [ c[z] : z in [1..l] ];
             c := Coordinates (MJ, MJ!(X[i] * Jbas[t]));
             mu[i][t] := [ c[z] : z in [1..l] ];
         end for;
     end for;

     /* write down the system of equations */
     mat := RMatrixSpace (F, n*l, n^2*l)!0;
     vec := VectorSpace (F, n^2*l)!0;
     for i in [1..n] do
         for j in [1..n] do
             for z in [1..l] do
                 col := (i-1)*n*l + (j-1)*l + z;
                 vec[col] := delta[i][j][z];
                 for s in [1..n] do
                    row := (s-1)*l + z;
                    mat[row][col] := mat[row][col] + beta[i][j][s];
                 end for;
                 for t in [1..l] do
                    row := (i-1)*l + t;
                    mat[row][col] := mat[row][col] - lambda[j][t][z];
                    row := (j-1)*l + t;
                    mat[row][col] := mat[row][col] - mu[i][t][z];
                 end for;
             end for;
         end for;
     end for;
       
     /* solve the system */
     isit, sol := IsConsistent (mat, vec);
     assert isit;
     
     /* modify <X> */
     Y := [];
     for i in [1..n] do
         c := [ sol[z] : z in [(i-1)*l+1..i*l] ];
         u := &+ [ c[z] * Jbas[z] : z in [1..l] ];
         Y[i] := X[i] + MA!u;
     end for;

return Y, sub < J | Basis (JJ) >;
end function;


/* the main function with optional boolean parameter "basis" */

__WedderburnDecomposition := function (A : basis := false) 

     if not basis then
         Abas := [ x : x in Basis (A) ];
     else
         Abas := [ A.i : i in [1..Ngens (A)] ];
     end if;

     k := BaseRing (A);
     d := Degree (A);
    
     // compute the Jacobson radical of <A>    
     J := JacobsonRadical (A);
     Jbas := [ x : x in Basis (J) ];     
       
     // first find a vector space complement to <J>
     MS := RMatrixSpace (k, d, d);
     AS := sub < MS | [ MS!(Abas[i]) : i in [1..#Abas] ] >;
     JS := sub < AS | [ AS!(Jbas[i]) : i in [1..#Jbas] ] >;
     XS := Complement (AS, JS);
     X := [ A!x : x in Basis (XS) ];
     B := sub < A | X >;
     
     // now refine the vector space complement to an algebra complement
     B := sub < A | X >;
     Y := X;
     K := J;
     while Dimension (K) gt 0 do
         Y, K := __Refine_WC (Y, K);       
     end while;
       
     B, fB := sub < A | Y >;
       
return sub < J | Jbas >, B;
end function;


/* a useful shortcut when one already has the Jacobson radical */

__WedderburnComplement := function (A, J : basis := false) 

     if not basis then
         Abas := [ x : x in Basis (A) ];
     else
         Abas := [ A.i : i in [1..Ngens (A)] ];
     end if;

     k := BaseRing (A);
     d := Degree (A);

     /* first find a vector space complement to <J> */
     MS := RMatrixSpace (k, d, d);
     Jbas := [ x : x in Basis (J) ];
     AS := sub < MS | [ MS!(Abas[i]) : i in [1..#Abas] ] >;
     JS := sub < AS | [ AS!(Jbas[i]) : i in [1..#Jbas] ] >;
     XS := Complement (AS, JS);
     
     /* refine vector space complement to an algebra complement */
     MA := MatrixAlgebra (k, d);
     X := [ MA!(XS.i) : i in [1..Ngens (XS)] ];
     B := sub < MA | X >;
     Y := X;
     K := J;
     while Dimension (K) gt 0 do
         Y, K := __Refine_WC (Y, K);       
     end while;
       
     W := sub < MA | Y >;
     // this is for convenience in later functions ....
     W := sub < MA | Basis (W) >;
     assert Ngens (W) eq Dimension (W);

return W;
end function;


                 /* ---- Taft decompositions ---- */

__semisimple_proj := function (MS, pos, x)
     c := Coordinates (MS, MS!x);
return &+[ c[i] * MS.i : i in [1..pos] ];
end function;


/* an alternative version coded by PAB on 6/1 as a warm up for char. 2 case */
__Taft_Decomposition := function (A)

     K := BaseRing (A);
     assert Characteristic (K) mod 2 eq 1;
     d := Degree (A);
     MS := KMatrixSpace (K, d, d);

     JA := JacobsonRadical (A);
     S := __WedderburnComplement (A, JA);
     J := JA;
     D := A;

     while exists { i : i in [1..Ngens (S)] | not (S.i @ A`Star in S) } do

          DS := KMatrixSpaceWithBasis ([MS!s : s in Basis (S)] cat [MS!j : j in Basis (J)]);
          pi := hom < D -> S | x :-> S!__semisimple_proj (DS, #Basis(S), x) >;
          rho := hom < S -> D | x :-> (x + (((x @ A`Star) @ pi) @ A`Star)) / 2 >;
          D := sub < Generic (A) | J * J , [ S.i @ rho : i in [1..Ngens (S)] ] >;
          J := JacobsonRadical (D);
          S := __WedderburnComplement (D, J);

     end while;

return JA, S;

end function;

// forms the quotient X/Y as a K-space
__TDS_Quotient_Space := function (X, Y)
     assert Y subset X;
     Q, f := quo<X|Y>;
     assert IsCommutative (Q);
     V := VectorSpace (BaseRing (X), Dimension (Q));
return V, hom < X -> V | x :-> V!Coordinates (Q, x @ f) >;
end function;

__TDS_Complement := function (X, Y)
     assert Y subset X;
     MS := KMatrixSpace (BaseRing (X), Degree (X), Degree (X));
     if Dimension(Y) eq 0 then 
          return KMatrixSpaceWithBasis ([ MS!x : x in Basis (X)]);
     else
          XS := KMatrixSpaceWithBasis ([ MS!x : x in Basis (X)]);
          YS := KMatrixSpaceWithBasis ([ MS!y : y in Basis (Y)]);
          assert YS subset XS;
     end if;
return Complement (XS, YS);
end function;

// in characteristic 2, find *-subring, B, of A with A^# = B^# 
__Taft_Decomposition_Subring := function (A)

     K := BaseRing (A);
     assert Characteristic (K) eq 2;
     d := Degree (A);
     MS := KMatrixSpace (K, d, d);

     J := JacobsonRadical (A);
     I := J;
     D := A;
     S := __WedderburnComplement (D, J);

//     while exists { i : i in [1..Ngens (S)] | not (S.i @ A`Star in S) } do

          // set up the infrastructure for the next lifting stage
          P := I * J;
"S is not yet *-invariant:";
"  dim(J/I) =", Dimension (J) - Dimension (I);
"  dim(J/P) =", Dimension (J) - Dimension (P);
          DS := KMatrixSpaceWithBasis ([MS!s : s in Basis (S)] cat [MS!j : j in Basis (J)]);
          pi := hom < D -> S | x :-> S!__semisimple_proj (DS, #Basis(S), x) >;
          dot := hom < S -> S | s :-> (s @ A`Star) @ pi >;
          V, f := __TDS_Quotient_Space (J, P);

          // set up the derivation <delta> : S --> J/P
          space := KMatrixSpace (K, Dimension (S), Dimension (V));
          delta := space!Matrix ([ ((S.i @ dot) @ A`Star - S.i) @ f : i in [1..Ngens (S)] ]);

          // set up the space of inner derivations S --> J/P coming from ker(tr)
          comp := __TDS_Complement (J, P);
          tr := Matrix ([ (Matrix(comp.i) + Matrix(comp.i) @ A`Star) @ f : i in [1..Ngens (comp)] ]);
          ker := Nullspace (tr);
          Z := [ Matrix (&+[ (ker.j)[l] * comp.l : l in [1..Ngens (comp)] ]) : 
                           j in [1..Ngens (ker)] ];
// sanity check 
assert forall { z : z in Z | z + z @ A`Star eq 0 };
          sol := sub < space | 
             [ Matrix ([ (S.i * z + z * S.i) @ f : i in [1..Ngens(S)] ]) : z in Z ] >;

          // the big question! 
          assert delta in sol;

          // if it is, find m in Z such that <delta> is the inner derivation of m
          // define hom from span(Z) to sol on generators so that there's a pull back map

 //    end while;
 "delta =", delta;
 "sol =", sol;


return A, _, _;
end function;



                 /* ---- intrinsics ---- */

intrinsic WedderburnDecomposition (A::AlgMat) -> AlgMat , AlgMat

   { Return a ring decomposition A = J + S, 
     where J is the Jacobson radical of A and S is semisimple } 
   
     k := BaseRing (A);
     require IsField (k) : "Base ring of argument 1 not a field";
   
return __WedderburnDecomposition (A : basis := false);

end intrinsic;


intrinsic MaximalDecomposition (A::AlgMat) -> AlgMat, AlgMat , AlgMat

   { Return a Taft decomposition of a *-ring, B, of A having the same group 
     of unitarian elements as A. In odd characteristic, B = A.}
     
     // PAB (6/1/2022) --- <AlgStar> should be a type
     require IsStarAlgebra (A) : 
            "argument does not have an assigned involution";

     require IsField (BaseRing (A)) : "Base ring of argument 1 not a field";

     if Characteristic (BaseRing (A)) ne 2 then 
          J, T := __Taft_Decomposition (A);
          B := A;
          B`Star := A`Star;
     else 
          B, J, T := __Taft_Decomposition_Subring (A);
 //         B`Star := hom < B -> B | x :-> x @ A`Star >;
     end if;

 //    J`Star := hom < J -> J | x :-> x @ A`Star >;
 //    T`Star := hom < T -> T | x :-> x @ A`Star >; 

return B;

end intrinsic;



        /* -------- intrinsics for group algebras ---------- */

intrinsic WedderburnDecomposition (A::AlgGrp) -> AlgGrpSub, AlgGrpSub

   { Return a ring decomposition A = J + S, 
     where J is the Jacobson radical of A and S is semisimple }

     MatA, phi, psi := GroupAlgebraAsMatrixStarAlgebra (A);

     MatJ, MatW := WedderburnDecomposition (MatA);

     J := sub < A | [ MatJ.i @ psi : i in [1..Ngens (MatJ)] ] >;
     W := sub < A | [ MatW.i @ psi : i in [1..Ngens (MatW)] ] >;

return J, W;

end intrinsic;


intrinsic TaftDecomposition (A::AlgGrp) -> AlgGrpSub, AlgGrpSub

  { Return a *-invariant Wedderburn decomposition of the *-ring A }

     if not IsStarAlgebra (A) then
         /* equip <A> with its natural involution */
         star := StarOnGroupAlgebra (A);
     end if; 

     MatA, phi, psi := GroupAlgebraAsMatrixStarAlgebra (A);

     MatJ, MatT := TaftDecomposition (MatA);

     J := sub < A | [ MatJ.i @ psi : i in [1..Ngens (MatJ)] ] >;
     T := sub < A | [ MatT.i @ psi : i in [1..Ngens (MatT)] ] >;

return J, T;

end intrinsic;




