// created by PAB on 6/8/2022
// neither a great name nor a great way to do it ...
intrinsic IsStarIdeal (A::AlgMat, P::AlgMat) -> BoolElt 
 { check if P is a *-ideal of A }
     require IsStarAlgebra (A) : "A must be a *-algebra";
     require forall { i : i in [1..Ngens (P)] | P.i in A } : 
          "P must be a subalgebra of A";
return
     forall { j : j in [1..Ngens (P)] | (P.j @ A`Star in P) and
          forall {i : i in [1..Ngens (A)] | (A.i * P.j in P) and (P.j * A.i in P) } };
end intrinsic;

intrinsic StarQuotient (A::AlgMat, P::AlgMat) -> AlgMat 
 { form the *-algebra A/P as a matrix *-algebra }
     require IsStarAlgebra (A) : "A must be a *-algebra";
     require IsStarIdeal (A, P) : "P must be a *-ideal of A";
     AmodP, pi := quo <A | P>;
     B, f := MatrixAlgebra (AmodP);
     // construct * induced on B 
     B`Star := hom <B -> B | b :-> ((((b @@ f) @@ pi) @ A`Star) @ pi) @ f >;
return B;
end intrinsic;

__semisimple_proj := function (MS, pos, x)
     c := Coordinates (MS, MS!x);
return &+[ c[i] * MS.i : i in [1..pos] ];
end function;

intrinsic InduceStar (A::AlgMat, S::AlgMat) -> AlgMat
 { induce the involution of *-algebra A on the semisimple complement S to the 
   radical J(A) }
   
     require S subset A : "S must be a subring of A";
   
     J := JacobsonRadical (A);
     
     require Dimension(J meet S) eq 0 : 
         "S must be a complement to the Jacobson radical of A";

     MS := KMatrixSpace (BaseRing (A), Degree (A), Degree (A));
     space := KMatrixSpaceWithBasis ([MS!s : s in Basis (S)] cat [MS!j : j in Basis (J)]);
     pi := hom < A -> S | x :-> S!(&+[ c[i] * space.i : i in [1..Dimension(S)] ]
                          where c is Coordinates (space, space!x)) >;
//     pi := hom < A -> S | x :-> S!__semisimple_proj (space, #Basis(S), x) >;
     dot := hom < S -> S | s :-> (s @ A`Star) @ pi >;
     S`Star := dot;
     
return S;
end intrinsic;