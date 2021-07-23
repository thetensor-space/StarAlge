/* 
  Created by PAB on 7/23/2021.

  Implementation of algorithms for isometry tests in the characteristic 2 case.
*/

__trace := function (A, z) return z + z @ A`Star; end function;

__norm := function (A, z) return (z @ A`Star) * z; end function;

__delta := function (A, z) return __trace (A, z) + __norm (A, z); end function;

intrinsic RadicalUnitarians (A::AlgMat) -> GrpMat
  { Return the subgroup of A^# lying within 1 + J(A). }

  d := Degree (A);
  F := BaseRing (A);
  one := Identity (A);

  J := JacobsonRadical (A);
  K := J;
  Gamma := sub < GL (d, F) | [ Identity (A) + J.i : i in [1..Ngens (J)] ] >;

  // begin with
  while Dimension (K) gt 0 do

// reassign <Gamma> and <K>
  end while;


return Gamma;

end intrinsic;