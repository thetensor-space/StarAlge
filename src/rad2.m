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

// for testing purposes: build a symmetric matrix of rank r
RandomSymmetricMatrix := function (F, d, r)
  Y := Random (MatrixAlgebra (F, r));
  Xr := Y + Transpose (Y);
  repeat
     i := Random ([1..r]);
     Xr[i][i] := Random (F);
  until Rank (Xr) eq r;
  X := MatrixAlgebra (F, d)!0;
  InsertBlock (~X, Xr, 1, 1);
  T := Random (GL (d, F));
return T * X * Transpose (T);
end function;

/*  
  stabilizer function requested by James in email 8/4/2021

  Given a polar space V and vector v in V, 
  compute the stabilizer of v inside Isom(V)
*/

__MyVectorStabilizerGL := function (u)
  U := Parent (u);
  n := Dimension (U);
  F := BaseRing (U);
  C := Complement (U, sub < U | u >);
  T := Matrix ([u] cat Basis (C));
  one := Identity (MatrixAlgebra (F, n));
  G := GL (n-1, F);
  gens := [ GL(n,F)!InsertBlock (one, G.i, 2, 2) : i in [1..Ngens (G)] ];
  for i in [2..n] do
    Z := one;
    Z[i][1] := F!1;
    Append (~gens, GL(n,F)!Z);
  end for;
  gens := [ T^-1 * gens[i] * T : i in [1..#gens] ];
  assert forall { g : g in gens | u * g eq u };
return sub < GL (n, F) | gens >;
end function;


__MyVectorStabilizerNondegenerate := function (U, u)

  n := Dimension (U);
  F := BaseRing (U);

  // case 1: u is anisotropic
  if InnerProduct (u, u) ne 0 then
"<info> v anisotropic";
    W := OrthogonalComplement (U, sub<U|u>);
    assert Dimension (W) eq n-1;
    T := Matrix ([u] cat Basis (W));
    X := InnerProductMatrix (U);
    Y := T * X * Transpose (T);
    Y0 := ExtractBlock (Y, 2, 2, n-1, n-1);
    W0 := VectorSpace (F, n-1, Y0);
    G := IsometryGroup (W0);
    one := Identity (MatrixAlgebra (F, n));
    gens := [ GL(n,F)!InsertBlock (one, G.i, 2, 2) : i in [1..Ngens (G)] ];

  // case 2: u is isotropic
  else
"<info> v isotropic";
    v := HyperbolicPair (U, u);
    W := OrthogonalComplement (U, sub<U|u,v>);
    assert Dimension (W) eq n-2;
    T := Matrix ([u] cat Basis (W) cat [v]);
    X := InnerProductMatrix (U);
    Y := T * X * Transpose (T);
    Y0 := ExtractBlock (Y, 2, 2, n-2, n-2);
    W0 := VectorSpace (F, n-2, Y0);
    G := IsometryGroup (W0);
    one := Identity (MatrixAlgebra (F, n));
    gens := [ GL(n,F)!InsertBlock (one, G.i, 2, 2) : i in [1..Ngens (G)] ];
    for i in [1..n-2] do
      Z := one;
      y := W0.i;
      x := y * Y0;
      InsertBlock (~Z, Transpose (Matrix (x)), 2, 1);
      InsertBlock (~Z, Matrix (y), n, 2);
      Append (~gens, GL(n,F)!Z);
    end for;

  end if;

  gens := [ T^-1 * gens[i] * T : i in [1..#gens] ];

  // check gens fix u
  assert forall { g : g in gens | u * g eq u };

  // check gens are isometries of U
Ngens (G);
[ IsIsometry (U, gens[i]) : i in [1..#gens] ];
  assert forall { g : g in gens | IsIsometry (U, g) };

return sub < GL (n, F) | gens >;

end function;


intrinsic VectorStabilizer (V::ModTupFld, v::ModTupFldElt) -> GrpMat 

{ The stabilizer of v in the group of isometries of the polar space V. }

  require IsPolarSpace (V) : "V must be equipped with an inner product";
  
  F := BaseRing (V);
  d := Dimension (V);
  X := InnerProductMatrix (V);
  R := Radical (V);
  r := Dimension (R);

  if r eq 0 then
    return __MyVectorStabilizerNondegenerate (V, v);
  end if;

  if v in R then

  "<info> v in R";

    C := Complement (V, R);
    T := Matrix (Basis (C) cat Basis (R));
    Y := T * X * Transpose (T);

    // get the part that actually needs to be stabilized
    vT := v * T^-1;
    assert forall { i : i in [1..d-r] | vT[i] eq 0 };
    u := Vector ([ vT[i] : i in [1+d-r..d] ]);
    H := __MyVectorStabilizerGL (u);

    // add in isometries of nondegenerate block
    Y0 := ExtractBlock (Y, 1, 1, d-r, d-r);
    V0 := VectorSpace (F, d-r, Y0);
    I0 := IsometryGroup (V0);

    // insert as blocks
    one := Identity (MatrixAlgebra (F, d));
    gens := [ GL(d,F)!InsertBlock (one, H.i, 1+d-r, 1+d-r) : i in [1..Ngens (H)] ];
    gens cat:= [ GL(d,F)!InsertBlock (one, I0.i, 1, 1) : i in [1..Ngens (I0)] ];

    // add in unipotent elements
    for i in [1..d-r] do 
      for j in [1+d-r..d] do
        Z := one;
        Z[i][j] := F!1;
        Append (~gens, GL(d,F)!Z);
      end for;
    end for;

    // check gens are isometries of Y
    assert forall { g : g in gens | g * Y * Transpose (g) eq Y };

    // check that gens stabilize vT
    assert forall { g : g in gens | vT * g eq vT };

    S := sub < GL (d, F) | [ T^-1 * g * T : g in gens ] >;

  else

  "<info> v outside R";

    C := Complement (V, R + sub < V | v >);
    T := Matrix ([v] cat Basis (C) cat Basis (R));
    Y := T * X * Transpose (T);

    // get the part that needs to be stabilized
    Y0 := ExtractBlock (Y, 1, 1, d-r, d-r);
    V0 := VectorSpace (F, d-r, Y0);
    H := __MyVectorStabilizerNondegenerate (V0, V0.1);   // v is 1st basis vector

    // insert as blocks
    one := Identity (MatrixAlgebra (F, d));
    gens := [ GL(d,F)!InsertBlock (one, H.i, 1, 1) : i in [1..Ngens (H)] ];
    // add in GL elements for radical
    G := GL (r, F);
    gens cat:= [ GL(d,F)!InsertBlock (one, G.i, 1+d-r, 1+d-r) : i in [1..Ngens (G)] ];

    // add in unipotent elements
    for i in [2..d-r] do    // not for 1st basis element
      for j in [1+d-r..d] do
        Z := one;
        Z[i][j] := F!1;
        Append (~gens, GL(d,F)!Z);
      end for;
    end for;

    // check gens are isometries of Y
    assert forall { g : g in gens | g * Y * Transpose (g) eq Y };

    // check that gens stabilize v*T
    assert forall { g : g in gens | v * T^-1 * g eq v * T^-1 };

    S := sub < GL (d, F) | [ T^-1 * g * T : g in gens ] >;
  
  end if;

  // sanity check that S is a subgroup of Isom(V)
  assert forall { i : i in [1..Ngens (S)] | IsIsometry (V, S.i) };

  // sanity check that S stabilizes v
  assert forall { i : i in [1..Ngens (S)] | v * S.i eq v };

return S;

end intrinsic;
  

