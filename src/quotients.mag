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