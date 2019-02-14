/* 
    Copyright 2013--2017, Peter A. Brooksbank, James B. Wilson.
    Distributed under GNU GPLv3.
*/



/*
  Given a system of forms, S, return a transition matrix that
  exhibits a fully-refined perp-decomposition of S. 
  
  Also return a partition of dimension of the underlying space 
  that indicates the block sizes of the perp-indecomposables.
*/

// Added the option to give the adjoint algebra if it has already been computed for S.

intrinsic PerpDecomposition (S::SeqEnum : Adjoint := 0) -> AlgMatElt, SeqEnum

  { Find a transition matrix that exhibits a fully-refined 
    perp-decomposition of the bilinear map associated to the
    system of forms S. }

     d := Degree (Parent (S[1]));
     k := BaseRing (Parent (S[1]));

     /* first compute the radical of <S> */
     rad := &meet { Nullspace (M) : M in S };
     r := Dimension (rad);
     comp := Complement (VectorSpace (k, d), rad);
     C1 := MatrixAlgebra (k, d)!Matrix (Basis (comp) cat Basis (rad));
     T := [ C1 * S[i] * Transpose (C1) : i in [1..#S] ];
     T := [ ExtractBlock (T[i], 1, 1, d-r, d-r) : i in [1..#T] ];

     /* next compute and recognise the adjoint algebra of <T> */
     if Type(Adjoint) eq RngIntElt then 
        A := AdjointAlgebra (T);
     else
        A := Adjoint; // currently cannot compute the adjoint algebra of a degenerate system, so this shouldn't be too painful.
     end if;
     assert RecogniseStarAlgebra (A);


/* ==== DELETE =================================================================
   My guess is that these cases are designed to 
    1. record the correct dimensions based on the star 
      a. if self-adjoint, record the dimension
      b. if star maps it to another prim-idem then record double the dim but
          only do this once!
    2. verify the idempotents are ordered exactly as you think they are.

    The current bug is because (2) is not met. In fact, idempotents @ A`Star is 
    note contained in idempotents. Here the band-aid fix, but there is a deeper
    error.
                                                  JFM   14-02-2019
============================================================================= */
// ==== ADDED ==================================================================
    if #S eq 1 then
      assert IsSimple(A);
      _, _, _, phi := RecogniseClassicalSSA(A);
      idems := A`StarAlgebraInfo`primitiveIdempotents;
      new_idems := idems @ phi;
      assert forall{I : I in new_idems | I^2 eq I}; 
      assert forall{I : I in new_idems | I @ A`Star in new_idems};
      assert &+new_idems eq Generic(A)!1;
      A`StarAlgebraInfo`primitiveIdempotents := new_idems;
    end if;
// =============================================================================

     /* next form a basis from the images of the 
        primitive self-adjoint idempotents of <A> */
     idempotents := A`StarAlgebraInfo`primitiveIdempotents;
     dims := [ ];
     bas := [ ];
     for i in [1..#idempotents] do
         e := idempotents[i];
         im := Image (e);
         bas cat:= Basis (im);
         if (e @ A`Star eq e) then
            /* <e> is self-adjoint */
            Append (~dims, Dimension (im));
         elif (i lt #idempotents) then
            if (e @ A`Star eq idempotents[i+1]) then
               /* symplectic */
               Append (~dims, 2 * Dimension (im));
            else
               assert e @ A`Star eq idempotents[i-1];
            end if;
         else
           assert e @ A`Star eq idempotents[i-1];
         end if;

     end for;

     /* construct the associated transition matrix */
     assert #bas eq (d - r);
     mat := Matrix (bas);
     assert Rank (mat) eq (d - r);
     C := MatrixAlgebra (k, d - r)!Matrix (bas);
     C2 := DiagonalJoin (C, Identity (MatrixAlgebra (k, r)));

return C2 * C1, dims;
end intrinsic;

// Added wrapper for tensors. JM
intrinsic PerpDecomposition( B::TenSpcElt ) -> AlgMatElt, SeqEnum
{ Find a transition matrix that exhibits a fully-refined perp-decomposition of the bilinear map B.}
  try
    A := AdjointAlgebra(B);
  catch err
    error "Cannot compute the adjoint *-algebra.";
  end try;
  return PerpDecomposition( SystemOfForms(B) : Adjoint := A );
end intrinsic;
