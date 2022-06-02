/*
 *  Created on 4/29/2022 by PAB.
 *  Examples and constructions for testing in characteristic 2.
*/

RandomStarAlgebraWithRadical := function (d, p, e)
  q := p^e;
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
    if (Dimension (J) gt 0) and (Dimension (J*J) gt 0) then    
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

