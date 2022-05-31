/* 
    Copyright 2013--2017, Peter A. Brooksbank, James B. Wilson.
    Distributed under GNU GPLv3.
*/


     /*--- File contains functios to handle simple *-algebras ---*/
  
import "prelims.m": __RF_SETUP, 
                    InducedAlgebra,
                    EltseqWithBasis,
                    IsomorphismWithField,
                    AlgebraIsomorphism;

import "form.m": __transform_form, 
                 StandardReflexiveForm,
                 IdentifyOrthogonalType;



__SSA_exchange_image := function (S, Frob)
     m := Nrows (S) div 2;
     X := ExtractBlock (S, 1, 1, m, m);
     Y := ExtractBlock (S, m+1, m+1, m, m);
     T := DiagonalJoin (FrobeniusImage (Transpose (Y), -Frob), 
                        FrobeniusImage (Transpose (X),  Frob));
return T;
end function;

__elementary_matrix := function (K, m, i, j)
     Eij := MatrixAlgebra (K, m)!0;
     Eij[i][j] := 1;
return Eij;
end function;


MySimpleStarAlgebra := function (name, d, K : Frob := 0)
   
     A := MatrixAlgebra (K, d);
     e := Degree (K) div 2;
     q := #K;
     r := Characteristic (K)^e;
    
     if name eq "exchange" then

         assert d mod 2 eq 0;
         m := d div 2;
         ma := MatrixAlgebra (K, m);
         ugens := [ DiagonalJoin (ma.i, ma!0) : i in [1..Ngens (ma)] ];
         lgens := [ DiagonalJoin (ma!0, ma.i) : i in [1..Ngens (ma)] ];
         A := sub < A | ugens cat lgens >;
         bst := "exchange";
         
         star := hom < A -> A | 
                      a :-> __SSA_exchange_image (a, Frob) >;
         
         gens := [ DiagonalJoin (x, FrobeniusImage (Transpose (x), Frob)^-1) : 
                                      x in Generators (GL (m, K)) ];
	 
         grp := sub < GL (d, K) | [ GL (d, K)!x : x in gens ] >;
         sgo := #GL (m, K);
         grp`Order := sgo;
         con := grp;
         cgo := sgo; 

         /* build primitive self-adjoint idempotents */
         idempotents := [ ];
         for i in [1..m] do
            E := __elementary_matrix (K, d, i, i);
            E +:= E @ star;
            Append (~idempotents, E);
         end for;
     
     else

         bst := "classical"; 

         if name eq "symplectic" then

            grp := Sp (d, K);
            con := CSp (d, q);

            /* build primitive self-adjoint idempotents */
            idempotents := [ ];
            for i in [1..(d div 2)] do
               E := __elementary_matrix (K, d, i, i);
               F := __elementary_matrix (K, d, d+1-i, d+1-i);
               Append (~idempotents, E);
               Append (~idempotents, F);
            end for;

         elif name eq "orthogonalcircle" then

            if d eq 1 then

                grp := sub < GL (1, K) | [ GL (1, K)![-1] ] >;
                con := GL (1, q);

                /* build primitive self-adjoint idempotents */
                idempotents := [ Identity (A) ];

            else

                grp := GO (d, K);
                con := CGO (d, q);
                con`Order := ((q - 1) div 2) * #grp;

                /* build primitive self-adjoint idempotents */
                F_orth := Identity (A);
                COB := TransformForm (F_orth, "orthogonalcircle");
                idempotents := [ ];
                for i in [1..d] do
                   E := __elementary_matrix (K, d, i, i);
                   Append (~idempotents, COB^-1 * E * COB);
                end for;

            end if;

         elif name eq "orthogonalplus" then

            grp := GOPlus (d, K);
            con := CGOPlus (d, q);
            con`Order := (q - 1) * #grp;

            /* build primitive self-adjoint idempotents */
            F_orth := Identity (A);
            if (q mod 4 eq 3) and (d mod 4 eq 2) then
               F_orth[1][1] := -1;
            end if;
            COB := TransformForm (F_orth, "orthogonalplus");
            idempotents := [ ];
            for i in [1..d] do
               E := __elementary_matrix (K, d, i, i);
               Append (~idempotents, COB^-1 * E * COB);
            end for;

         elif name eq "orthogonalminus" then
            grp := GOMinus (d, K);
            con := CGOMinus (d, q);
            /* Magma does not currently store order of GOMinus */
            ord := 2 * q^((d*(d-2)) div 4) * (q^(d div 2) + 1);
            if (d gt 2) then
	        ord *:= &* [ q^(2*i) - 1 : i in [1..(d div 2) - 1] ];    
            end if;
            grp`Order := ord;
            con`Order := (q - 1) * ord;
            /* build primitive self-adjoint idempotents */
            F_orth := Identity (A);
            if (q mod 4 eq 1) or (d mod 4 eq 0) then
//               F_orth[1][1] := K.1;  // a non-square
// fix by PAB on 08/14/16 
F_orth[1][1] := PrimitiveElement (K);
            end if;
            COB := TransformForm (F_orth, "orthogonalminus");
            idempotents := [ ];
            for i in [1..d] do
               E := __elementary_matrix (K, d, i, i);
               Append (~idempotents, COB^-1 * E * COB);
            end for;

         else

            assert name eq "unitary";
            grp := GU (d, K);      
            con := CGU (d, r);
            con`Order := (r - 1) * #grp;

            /* build primitive self-adjoint idempotents */
            F_orth := Identity (A);
            COB := TransformForm (F_orth, "unitary");
            idempotents := [ ];
            for i in [1..d] do
               E := __elementary_matrix (K, d, i, i);
               Append (~idempotents, COB^-1 * E * COB);
            end for;

         end if;
           
         M := StandardReflexiveForm (name, d, K);
         Mi := M^-1;
           
         if name eq "unitary" then
	
            star := hom < A -> A | a :-> 
                        Transpose (Mi * FrobeniusImage (a, e) * M) >;
         else
           
            star := hom < A -> A | a :-> M * Transpose (a) * Mi >;
         
         end if;
         sgo := #grp;
         cgo := #con;

     end if;
       
     /* check that we have self-adjoint idempotents */

// commented out 5/6/2011: we only want the sum of the idempotents to be
// self-adjoint in the symplectic case.

//assert forall { x : x in idempotents | (x^2 eq x) and (x @ star eq x) };
//"number of primitive self-adjoint idempotents =", #idempotents;
     
     RF_SAI := __RF_SETUP ("algebra");
                         
     RF_SSI := __RF_SETUP ("simple");
       
     SAI_data := rec < RF_SAI | >;
     SAI_data`isSimple := true;
     SAI_data`isSemisimple := true;
     SAI_data`jacobsonRadical := sub < A | A!0 >;
     SAI_data`taftComplement := A;
     SAI_data`srComponents := < A >;
     SAI_data`srDegrees := [ Degree (A) ];
     SAI_data`basicSimpleTypes := bst;
     SAI_data`sharpGroupOrder := sgo;
     SAI_data`sharpGroupGenerators := [ A!(grp.i) : 
                                          i in [1..Ngens (grp)] ];
     SAI_data`normaliserOrder := cgo;
       /* the fields are sometimes incompatible */
       Embed (BaseRing (A), BaseRing (con));
       Embed (BaseRing (con), BaseRing (A));
     SAI_data`normaliserGenerators := [ Generic (A)!(con.i) : 
                                          i in [1..Ngens (con)] ];
     SAI_data`primitiveIdempotents := idempotents;
     
     SSI_data := rec < RF_SSI | >;
     SSI_data`simpleParameters := < name , d , #K >;
     SSI_data`standardSimple := A;
if bst eq "classical" then
SSI_data`reflexiveForm := M;
end if;
     SSI_data`standardIsomorphism := hom < A -> A | a :-> a >;
     SSI_data`standardInverse := hom < A -> A | a :-> a >;
     SSI_data`sharpGroup := grp;
     SSI_data`sharpGroupOrder := sgo;
     SSI_data`conformalGenerators := [ Generic (A)!(con.i) : 
                                          i in [1..Ngens (con)] ];
     SSI_data`conformalGroupOrder := cgo;
     SSI_data`fieldAutoGenerator := Identity (A);
     SSI_data`centraliserGenerators := [ Identity (A) ];
                            
     A`Star := star;
     A`StarAlgebraInfo := SAI_data;
     A`StarSimpleInfo := SSI_data;

return A;
end function;


/*
   This intrinsic function returns the standard copy of the 
   simple *-algebra for the given input parameters.
*/

intrinsic SimpleStarAlgebra (name::MonStgElt, d::RngIntElt, 
                                  K::FldFin) -> AlgMat

   { Return the standard *-simple algebra with input defining parameters }

     require name in [ "exchange" , "symplectic" , "unitary" ,
                       "orthogonalplus" , "orthogonalminus" , 
                       "orthogonalcircle" ] :
     "argument 1 does not specify the type of a simple *-algebra";

     if name eq "unitary" then
         require Degree (K) mod 2 eq 0 : 
           "simple *-algebras of unitary type
            are only defined for fields of even degree";
     end if;

return MySimpleStarAlgebra (name, d, K);

end intrinsic;



__T_to_I := function (COB, conj, y)
     x := DiagonalJoin (< conj[i]^-1 * y * conj[i] : 
                                     i in [1..#conj] >);
return COB^-1 * x * COB;
end function;

__map_on_modules := function (I)

     M := RModule (I);
     irreds := IndecomposableSummands (M);
     m := #irreds;

     /* deal with the simple case */
     if #irreds eq 1 then
         isit, X, f := IsAbsolutelyIrreducible (M);
         if isit then
   	        X := BaseRing (I).1 * Identity (I);
            f := 1;
         end if;
         centGens := [ X ];
         centOrder := #BaseRing (I)^f - 1;
         domain := Generic (I);
         image := Generic (I);
         return hom < domain -> image | x :-> x >, 
	        hom < image -> domain | y :-> y >,
	        centGens, centOrder;
     end if;

     assert #Set ([ Dimension (E) : E in irreds ]) eq 1; 
     e := Dimension (irreds[1]);
     basis := &cat [ Basis (E) : E in irreds ];
     COB := Generic (I)!Matrix (basis);
     J := sub < Generic (I) | 
                [ COB * I.i * COB^-1 : i in [1..Ngens (I)] ] >;

     /* extract modules as blocks from <J> */
     modules := [ ];
     T := MatrixAlgebra (BaseRing (I), e);
     for i in [1..#irreds] do
	    Xi := [ ExtractBlock (J.j, 1+e*(i-1), 1+e*(i-1), e, e) :
			     j in [1..Ngens (J)] ];
        Ji := sub < T | Xi >;
        Mi := RModule (Ji);
        Append (~modules, Mi);
     end for;

     /* construct isomorphisms between modules in <modules> */
     U := modules[1];
     conj := [ Identity (T) ];
     for i in [2..#modules] do
         Mi := modules[i];
         isit, Ci := IsIsomorphic (U, Mi);
         assert isit;
         Append (~conj, Ci);
     end for;

     /* construct the group of elements centralising <I> */
     isit, X, f := IsAbsolutelyIrreducible (U);
     if isit then
         X := Identity (MatrixAlgebra (BaseRing (I), e));
     end if;
     EnvX, K, a, b := IsomorphismWithField (X);
     C := GL (m, K);
     centGens := [ ];
     Z := Generic (I)!0;
     for t in [1..Ngens (C)] do
         y := C.t;
         Y := Z;
         for i in [1..m] do
            for j in [1..m] do
               block := conj[i] * conj[j]^-1 * (y[i][j] @ b);
	       InsertBlock (~Y, block, (i-1)*e + 1, (j-1)*e + 1); 
	    end for;
         end for;
         Append (~centGens, Y);
     end for;

     /* construct the domain and image of the map */
     image := T;
     dom_gens := [ DiagonalJoin (
                < conj[j]^-1 * T.i * conj[j] : j in [1..#conj] >
                                ) : i in [1..Ngens (T)] ];
     domain := sub < Generic (I) | 
              [ COB^-1 * dom_gens[j] * COB : j in [1..#dom_gens] ] >;

     /* construct the inverse isomorphisms */
     phi := hom < domain -> image |
                 x :-> ExtractBlock (COB * x * COB^-1, 1, 1, e, e) >;
     psi := hom < image -> domain | y :-> __T_to_I (COB, conj, y) >;

return phi, psi, centGens, #C;
end function;


/*
   Given a minimal ideal <I> of a semisimple *-algebra <A>, of basic 
   type <btype>, find a simple *-algebra <S> in semi-reduced form that 
   is isomorphic to <I> together with inverse isos <I> -> <S>.
   
   Assume that the generators of <I> form a basis.
   
   For exchange type we assume basis elements m+1..2m are the
   *-images of basis elements 1..m
*/

/* 
   This function was replaced on 1/4/2011 so that elements in 
   overalgebras of the simple components could be lifted.
*/

__RSSA_semi_reduced := function (I, btype)

     if (btype eq "classical") then

	ItoS, StoI, centGens, centOrder := __map_on_modules (I);
        ims := [ I.i @ ItoS : i in [1..Ngens (I)] ];
        S := sub < Parent (ims[1]) | ims >;
        
      else  

        /* put <I> into block form */         
        n := Ngens (I);
        assert (n mod 2 eq 0);
        m := n div 2;
        I1 := sub < Generic (I) | [ I.i : i in [1..m] ] >;
        I2 := sub < Generic (I) | [ I.i : i in [m+1..n] ] >;
        V := VectorSpace (BaseRing (I), Degree (I));
        W1 := sub < V | [ Image (I1.i) : i in [1..m] ] >;
        W2 := sub < V | [ Image (I2.i) : i in [1..m] ] >;
        W1bas := Basis (W1);
        W2bas := Basis (W2);
        COB := Generic (I)!Matrix (W1bas cat W2bas);
        J := sub < Generic (I) | 
                   [ COB * I.i * COB^-1 : i in [1..Ngens (I)] ] >; 
        w1 := #W1bas;
        w2 := #W2bas;
        T1 := MatrixAlgebra (BaseRing (I), w1);
        T2 := MatrixAlgebra (BaseRing (I), w2);
        J1 := sub < T1 | 
           [ ExtractBlock (J.i, 1, 1, w1, w1) : i in [1..m] ] >;
        J2 := sub < T2 |
           [ ExtractBlock (J.i, w1+1, w1+1, w2, w2) : 
                                            i in [m+1..2*m] ] >;

        /* handle each block separately */
        phi1, psi1, centGens1, centOrder1 := __map_on_modules (J1);
        phi2, psi2, centGens2, centOrder2 := __map_on_modules (J2);

        centOrder := centOrder1 * centOrder2;


        /* build the centraliser generators */
        centGens := [ ];
        for i in [1..#centGens1] do
	       Append (~centGens, DiagonalJoin (centGens1[i], Identity (T2)));
        end for;
        for j in [1..#centGens2] do
	       Append (~centGens, DiagonalJoin (Identity (T1), centGens2[j]));
        end for;

        /* form the image of <I> and its parent */
        ims1 := [ J1.j @ phi1 : j in [1..Ngens (J1)] ];
        ims2 := [ J2.j @ phi2 : j in [1..Ngens (J2)] ];
        Z1 := Parent (ims1[1])!0;
        Z2 := Parent (ims2[1])!0;
        ims := [ DiagonalJoin (ims1[i], Z2) : i in [1..#ims1] ];
        ims cat:= [ DiagonalJoin (Z1, ims2[i]) : i in [1..#ims2] ];
        S := sub < Parent (ims[1]) | ims >;
        ParSgens := [ DiagonalJoin (Domain (psi1).i, Z2) : 
			     i in [1..Ngens (Domain (psi1))] ];
        ParSgens cat:= [ DiagonalJoin (Z1, Domain (psi2).i) : 
			     i in [1..Ngens (Domain (psi2))] ];
        ParS := sub < Parent (ParSgens[1]) | ParSgens >;

        /* form the parent of <I> */
        D1 := Domain (phi1);
        D2 := Domain (phi2);
        Z1 := D1!0;
        Z2 := D2!0;
        ParJgens := [ DiagonalJoin (D1.i, Z2) : 
                            i in [1..Ngens (D1)] ];
        ParJgens cat:= [ DiagonalJoin (Z1, D2.i) : 
                            i in [1..Ngens (D2)] ];
        ParJ := sub < Parent (ParJgens[1]) | ParJgens >;
        ParI := sub < Generic (ParJ) | [ COB^-1 * ParJ.j * COB :
				      j in [1..Ngens (ParJ)] ] >;

        /* organise the inverse isomorphisms */
        ItoS := hom < ParI -> ParS | 
                        x :-> DiagonalJoin (x1 @ phi1, x2 @ phi2)
                  where x1 := 
               ExtractBlock (COB * x * COB^-1, 1, 1, w1, w1)
                  where x2 := 
               ExtractBlock (COB * x * COB^-1, w1+1, w1+1, w2, w2) 
                    >;

        s1 := Degree (Domain (psi1));
        s2 := Degree (Domain (psi2));

        StoI := hom < ParS -> ParI | 
                        y :-> COB^-1 * DiagonalJoin (y1, y2) * COB
                  where y1 := 
                       ExtractBlock (y, 1, 1, s1, s1) @ psi1
                  where y2 := 
                       ExtractBlock (y, s1+1, s1+1, s2, s2) @ psi2
                    >;

        centGens := [ COB^-1 * centGens[i] * COB : i in [1..#centGens] ];

     end if;

     /* induce the involution on <S> */
     star := hom < S -> S | r :-> ((r @ StoI) @ I`Star) @ ItoS >; 
     S`Star := star;

return true, S, ItoS, StoI, centGens, centOrder;

end function;




    /* ---- recognition functions for simple *-algebras ---- */


/* ---- classical type recognition function ---- */

__preimage := function (ms, MS, y)
     k := BaseRing (ms);
     c := Coordinates (MS, MS!y);
     coords := [];
     for a in c do
         coords cat:= Eltseq (a, k);
     end for;
return &+[ coords[i] * ms.i : i in [1..Ngens (ms)] ];
end function;

__image := function (MS, ms, y)
     K := BaseRing (MS);
     e := Degree (K) div Degree (BaseRing (ms));
     c := Coordinates (ms, ms!y);
     m := Dimension (ms) div e;
     coords := [ SequenceToElement ([ c[(j-1)*e+t] :
                           t in [1..e] ], K) : j in [1..m] ];
return &+[ coords[i] * MS.i : i in [1..Ngens (MS)] ];
end function;

intrinsic RecogniseClassicalSSA (S::AlgMat) -> BoolElt, AlgMat, Map, Map

   { Constructively recognise the simple *-algebra S of classical type }

     require IsStarAlgebra (S) : "argument has no assigned involution";

     /* check to see if <S> has already been recognised */
     if assigned (S`StarSimpleInfo) then
        SSI_data := S`StarSimpleInfo;
        if assigned SSI_data`simpleParameters then
           if SSI_data`simpleParameters[1] eq "exchange" or   
              SSI_data`simpleParameters[1] eq "twistedexchange" 
              then
  	      "[Recognise Exchange]: input has exchange type";  
              return false, _, _, _;
           else
	      return true, SSI_data`standardSimple,
                     SSI_data`standardIsomorphism, 
                     SSI_data`standardInverse;
           end if;
        end if;
     else
        RF_SSI := __RF_SETUP ("simple");
        SSI_data := rec < RF_SSI | >;
     end if;

     /* see if <S> has its *-algebra data structure set up */
     if assigned (S`StarAlgebraInfo) then
        SAI_data := S`StarAlgebraInfo;
        if assigned SAI_data`isSimple then
           if not SAI_data`isSimple then
	      "[Recognise Exchange]: must be simple";
	      return false, _, _, _;
           end if;
        end if;
     else
        RF_SAI := __RF_SETUP ("algebra");
        SAI_data := rec < RF_SAI | >;
     end if;
       
     require Type (BaseRing (S)) eq FldFin :
        "Base ring of argument is not a finite field";

     /* ensure the generators of <S> form a basis */
     if assigned (S`IsBasis) then
         if not S`IsBasis then
            bas := Basis (S);
            star := Star (S);
            S := sub < Generic (S) | bas >;
            S`Star := star;
         end if;
     else
         bas := Basis (S);
         star := S`Star;
         S := sub < Generic (S) | bas >;
         S`Star := star;
     end if;

     /* ensure that <S> does not act trivially on a subspace */
     if Dimension (&meet [ Nullspace (S.i) : i in [1..Ngens (S)] ]) gt 0 then
     "[Recognise Classical]: there is a faithful action on a smaller module";
         return false, _, _, _;
     end if;

     /* reduce to semi-reduced form */
     M := RModule (S);
     if IsIrreducible (M) then
         RED := S; 
         phi := hom < Generic (S) -> Generic (RED) | r :-> r >;
         psi := hom < Generic (RED) -> Generic (S) | r :-> r >;
     else
         flag, RED, StoRED, REDtoS, centraliserGenerators, centraliserOrder := 
                          __RSSA_semi_reduced (S, "classical");
         if not flag then
  	    "[Recognise Classical]: conversion to semi-reduced form failed";
            return false, _, _, _;
         end if;
         phi := StoRED;
         psi := REDtoS;
     end if;

            /*---- reduction to natural rep ----*/

     k := BaseRing (RED);
     d := Degree (RED);
     M := RModule (RED);
     isit, X, e := IsAbsolutelyIrreducible (M);
     if isit then
        X := Identity (Generic (RED));
        e := 1;
     end if;
     if Degree (S) eq Degree (RED) then 
         /* <S> is irreducible: assign centraliser gens */
         centraliserGenerators := [ X ];
         centraliserOrder := (#k)^e - 1;
     end if;
     mX := MinimalPolynomial (X);

     normaliserGenerators := centraliserGenerators;
     normaliserOrder := centraliserOrder;
       
     /* construct iso with algebra over correct field */
     RED_bas := Basis (RED);
     m := d div e;
     if (#RED_bas ne e * m^2) then
        return false, _, _, _;
     end if;
     ms := KMatrixSpace (k, d, d);
     Xbas := [];
     for i in [1..#RED_bas div e] do
         assert exists (s){ t : t in [1..#RED_bas] | 
                       not RED_bas[t] in sub < ms | Xbas > };
         Xbas cat:= [ RED_bas[s]*(X^z) : z in [0..e-1] ];
     end for;

     K := ext < k | mX >;
     V := VectorSpace (k, d);
     bas := [ (V.1) * X^t : t in [0..e-1] ];
     for i in [1..m-1] do
         assert exists (j){ k : k in [1..d] |
                 not V.k in sub < V | bas > };
         bas cat:= [ (V.j) * X^t : t in [0..e-1] ];
     end for;    
     W := VectorSpaceWithBasis (bas);

     /* construct the generator for Aut(<K>) as matrix over <k> */
     AutK_vecs := [ EltseqWithBasis (K, k, [(K.1)^i : i in [0..e-1]], 
		   Frobenius ((K.1)^i, Degree (k))) : i in [0..e-1] ];
     AutK_action := MatrixAlgebra (k, e)!Matrix (AutK_vecs); 
     AutK_generator := DiagonalJoin (< AutK_action : i in [1..m] >);
     COB := MatrixAlgebra (k, d)!Matrix (bas);
     AutK_generator := COB^-1 * AutK_generator * COB;
     AutK := AutK_generator @ psi;

assert forall { i : i in [1..Ngens (S)] | AutK * S.i * AutK^-1 in S };
//assert forall { i : i in [1..Ngens (S)] | 
//   AutK * (S.i @ S`Star) * AutK^-1 eq (AutK * S.i * AutK^-1) @ S`Star }; 

     normaliserGenerators cat:= [ AutK ];
     normaliserOrder *:= e;

     MA := MatrixAlgebra (K, m);
     B := [ ];
     for i in [1..#Xbas] do
         x := Xbas[i];
         xx := [];
         for j in [1..m] do
             v := W.(1+(j-1)*e) * x;
             c := Coordinates (W, v);
             vec := [ SequenceToElement ([ c[(j-1)*e+t] :
                           t in [1..e] ], K) : j in [1..m] ];
             xx cat:= vec;
         end for;
         Append (~B, MA!xx);
     end for;
            
     NAT := sub < MA | B >;
    
     MS := KMatrixSpace (K, m, m);
     MS := KMatrixSpaceWithBasis ([MS!B[(i-1)*e+1] : i in [1..#B div e]]);     
     ms := KMatrixSpaceWithBasis ([ms!x : x in Xbas]);
     
     NATtoRED := hom < NAT -> RED | r :-> RED!__preimage (ms, MS, r) >;
     REDtoNAT := hom < RED -> NAT | r :-> NAT!__image (MS, ms, r) >;

     /* induce the star on <NAT> and modify maps */
     NAT`Star := hom < NAT -> NAT | 
                        r :-> ((r @ NATtoRED) @ RED`Star) @ REDtoNAT >;
     phi := hom < S -> NAT | r :-> (r @ phi) @ REDtoNAT >;
     psi := hom < NAT -> S | r :-> (r @ NATtoRED) @ psi >;
    
     /* determine the basic type of the classical form */
     l := Degree (K);
     s := K.1 * Identity (NAT);
     ss := s @ NAT`Star;
     if s eq ss then 
         bt := 1;
     else
         assert l mod 2 eq 0;
         e := l div 2;
         assert s eq FrobeniusImage (ss, e);
         bt := -1;
         name := "unitary";
     end if;

     if Degree (NAT) gt 1 then
     
         /* set up the dual module */
         M := RModule (NAT);
         gens := [ Transpose (NAT.i @ NAT`Star) : i in [1..Ngens (NAT)] ];
         if bt eq -1 then
            gens := [ FrobeniusImage (gens[i], e) : i in [1..#gens] ];
         end if;
         D := sub < Generic (NAT) | gens >;
         N := RModule (D);

         /* test for isomorphism with <M> */
         isit, X := IsIsomorphic (M, N);
         if not isit then
            "[Recognise Classical]: not of classical type";
            return false, _, _, _;
         end if;


         /* identify the classical type of <X> */
         if (bt eq 1) then

            if (X eq Transpose (X)) and (Characteristic (k) ne 2) then 
	            if Nrows (X) eq 1 then
	                name := "orthogonalcircle";
                   C := MatrixAlgebra (K, 1)![1];
               else
                   name, C := IdentifyOrthogonalType (X);
               end if;
            else
               assert X eq -Transpose (X);
               name := "symplectic";
               C := __transform_form (X, Nrows (X), #K, name);
            end if;

         else

            diag := exists (i){ s : s in [1..Nrows (X)] | X[s][s] ne 0 };
            if diag then
               X := (1/X[i][i]) * X;
            else
	       flag := exists (i,j){ <s,t> : 
                         s in [1..Nrows (X)], t in [1..Nrows (X)] | 
                            X[s][t] ne 0 and X[s][t] + X[t][s] ne 0 };
               if flag then
                  X := (1/(X[i][j] + X[j][i])) * X;
               else
 		  if (K.1 + Frobenius (K.1, e) eq 0) then
		     "(1)";
		     X := K.1 * X;
	          else
		     "(2)";
                     X := (1 - 2*K.1/(K.1 + Frobenius (K.1, e))) * X;
                  end if;
               end if;
            end if;
            assert Transpose (X) eq FrobeniusImage (X, e);
            C := __transform_form (X, Nrows (X), #K, name); 

         end if;

     else

         /* in degree 1 any NAT is the standard copy */

         if not assigned (name) then
            name := "orthogonalcircle";
         end if;
         C := Identity (NAT);

     end if;

     Cinv := C^-1;
     STAN := SimpleStarAlgebra (name, Degree (NAT), K); 
     NATtoSTAN := hom < NAT -> STAN | r :-> Cinv * r * C >;
     STANtoNAT := hom < STAN -> NAT | r :-> C * r * Cinv >;    

     /* compose maps and assemble data structure */
     phi := hom < S -> STAN | r :-> (r @ phi) @ NATtoSTAN >;
     psi := hom < STAN -> S | r :-> (r @ STANtoNAT) @ psi >;

     /* construct normaliser generators for <RED> */

     normaliserOrder *:= STAN`StarAlgebraInfo`normaliserOrder;
//"order check:", normaliserOrder mod (#K - 1) eq 0;
     normaliserOrder div:= (#K - 1);
     STAN_normGens := STAN`StarAlgebraInfo`normaliserGenerators;
     conformalGenerators := [ x @ psi : x in STAN_normGens ];

assert forall { c : c in conformalGenerators |
  forall { i : i in [1..Ngens (S)] | c * (S.i) * c^-1 in S } };
assert forall { c : c in conformalGenerators |
  forall { i : i in [1..Ngens (S)] | c * (S.i @ S`Star) * c^-1 eq
           (c * S.i * c^-1) @ S`Star } };

     normaliserGenerators cat:= conformalGenerators;
   
     SSI_data`simpleParameters := STAN`StarSimpleInfo`simpleParameters;
     SSI_data`standardSimple := STAN;
     SSI_data`conformalGenerators := conformalGenerators;
     SSI_data`fieldAutoGenerator := AutK;
     SSI_data`centraliserGenerators := centraliserGenerators;
     SSI_data`standardIsomorphism := phi;
     SSI_data`standardInverse := psi;
     
     SAI_data`isSimple := true;
     SAI_data`isSemisimple := true;
     SAI_data`jacobsonRadical := sub < Generic (S) | S!0 >;
     SAI_data`taftComplement := S;
     SAI_data`srComponents := < S >;
     SAI_data`srDegrees := [ Degree (S) ];
     SAI_data`basicSimpleTypes := < "classical" >;

     SAI_data`normaliserGenerators := normaliserGenerators;
     SAI_data`normaliserOrder := normaliserOrder;
     SAI_data`primitiveIdempotents := 
       [ x @ psi : x in STAN`StarAlgebraInfo`primitiveIdempotents ];
    
     S`StarAlgebraInfo := SAI_data;
     S`StarSimpleInfo := SSI_data;

return true, STAN, phi, psi;
end intrinsic;


/* exchange type recognition function */

__AtoB := function (A, B, a)
     ms := KMatrixSpace (BaseRing (A), Degree (A), Degree (A));
     msA := KMatrixSpaceWithBasis ([ ms!(A.i) : i in [1..Ngens (A)] ]);
     c := Coordinates (msA, msA!a);
return &+ [ c[i] * B.i : i in [1..#c] ];
end function;

__BtoA := function (A, B, e, q, b)
     m := Degree (B) div 2;
     K := BaseRing (B);
     bas1 := [ (K.1)^t : t in [0..e-1] ];
     bas2 := [ (K.1)^(q*t) : t in [0..e-1] ];
     k := BaseRing (A);
     ms := KMatrixSpace (BaseRing (B), m, m);
     gens1 := [ ExtractBlock (B.(1+(i-1)*e), 1, 1, m, m) :  
                                              i in [1..m^2] ];
     gens2 := [ ExtractBlock (B.(1+(i-1)*e), m+1, m+1, m, m) :  
                                              i in [1+m^2..2*m^2] ];
     ms1 := KMatrixSpaceWithBasis ([ ms!gens1[i] : i in [1..m^2] ]);
     ms2 := KMatrixSpaceWithBasis ([ ms!gens2[i] : i in [1..m^2] ]);
     c1 := Coordinates (ms1, ms!ExtractBlock (b, 1, 1, m, m));
     c2 := Coordinates (ms2, ms!ExtractBlock (b, m+1, m+1, m, m));
     cc1 := &cat [ EltseqWithBasis (K, k, bas1, c1[i]) : i in [1..m^2] ];
     cc2 := &cat [ EltseqWithBasis (K, k, bas2, c2[i]) : i in [1..m^2] ];
     c := cc1 cat cc2;
return &+ [ c[i] * A.i : i in [1..Ngens (A)] ];
end function;


intrinsic RecogniseExchangeSSA (S::AlgMat) -> BoolElt, AlgMat, Map, Map

   { Constructively recognise the simple *-algebra S of exchange type }

     require IsStarAlgebra (S) : "argument has no assigned involution";

     /* check to see if <S> has already been recognised */
     if assigned (S`StarSimpleInfo) then
        SSI_data := S`StarSimpleInfo;
        if assigned SSI_data`simpleParameters then
           if SSI_data`simpleParameters[1] eq "exchange" or   
              SSI_data`simpleParameters[1] eq "twistedexchange" 
              then
              return true, SSI_data`standardSimple, 
                     SSI_data`standardIsomorphism, 
                     SSI_data`standardInverse;
           else
  	      "[Recognise Exchange]: input has classical type";
              return false, _, _, _;
           end if;
        end if;
     else
        RF_SSI := __RF_SETUP ("simple");
        SSI_data := rec < RF_SSI | >;
     end if;
 
     /* see if *-algebra data structure has been set up */    
     if assigned (S`StarAlgebraInfo) then
        SAI_data := S`StarAlgebraInfo;
        if assigned SAI_data`isSimple then
           if not SAI_data`isSimple then
	      "[Recognise Exchange]: must be simple";
              return false, _, _, _;
           end if;
        end if;
     else
        RF_SAI := __RF_SETUP ("algebra");
        SAI_data := rec < RF_SAI | >;
     end if;
       
     require Type (BaseRing (S)) eq FldFin : 
        "Base ring of argument is not a finite field"; 

     /* ensure the generators of <S> form a basis */
     star := S`Star;
     if assigned (S`IsBasis) then
         if not S`IsBasis then
            bas := Basis (S);
            S := sub < Generic (S) | bas >;
         end if;
     else
         bas := Basis (S);
         S := sub < Generic (S) | bas >;
     end if;
     S`Star := star; 

     /* ensure that <S> does not act trivially on a subspace */
     if Dimension (&meet [ Nullspace (S.i) : i in [1..Ngens (S)] ]) gt 0 then
     "[Recognise Exchange]: there is a faithful action on a smaller module";
         return false, _, _, _;
     end if;   

     /* reduce to semi-reduced form */
     flag, RED, StoRED, REDtoS, centraliserGenerators, centraliserOrder := 
         __RSSA_semi_reduced (S, "exchange");
     if not flag then
         "[Recognise Exchange]: conversion to semi-reduced form failed";
         return false, _, _, _;
     end if;
     phi := StoRED;
     psi := REDtoS;

     normaliserGenerators := centraliserGenerators;
     normaliserOrder := centraliserOrder;

              /* ---- reduce to natural rep ---- */

     k := BaseRing (RED);
     p := Characteristic (k);
     d := Degree (RED);
     
     /* find the minimal ideals of <C> */
     mins := MinimalIdeals (RED);
     if (#mins ne 2) then
         "[Recognise Exchange]: wrong number of minimal ideals";
         return false, _, _, _;
     end if;
     I := mins[1];
     J := mins[2];

     /* conjugate so that the ideals are in block diagonal form */
     imI := &+ [ Image (I.t) : t in [1..Ngens (I)] ];
     imJ := &+ [ Image (J.t) : t in [1..Ngens (J)] ];
     COB := Generic (RED)!Matrix (Basis (imI) cat Basis (imJ));
     COBinv := COB^-1;
     Ibas := Basis (I);
     Jbas := [ Ibas[t] @ RED`Star : t in [1..#Ibas] ];
     I := sub < Generic (RED) | 
                [ COB * Ibas[t] * COBinv : t in [1..#Ibas] ] >;
     J := sub < Generic (RED) | 
                [ COB * Jbas[t] * COBinv : t in [1..#Jbas] ] >;
     D := sub < Generic (RED) | [ I.t : t in [1..Ngens (I)] ] cat
                              [ J.t : t in [1..Ngens (J)] ] >;
     D`IsBasis := true;
     ParRED := Domain (REDtoS);
     ParD := sub < Generic (D) | 
		[ COB * ParRED.i * COB^-1 : i in [1..Ngens (ParRED)] ] >;
     REDtoD := hom < ParRED -> ParD | r :-> COB * r * COBinv >;
     DtoRED := hom < ParD -> ParRED | r :-> COBinv * r * COB >;
     D`Star := hom < D -> D | r :-> ((r @ DtoRED) @ RED`Star) @ REDtoD >;

     /* update <phi> and <psi> */ 
     ParS := Domain (phi);
     phi := hom < ParS -> ParD | r :-> (r @ phi) @ REDtoD >;
     psi := hom < ParD -> ParS | r :-> (r @ DtoRED) @ psi >;


           /* ---- work with <D> now --- */

     /* find an element of <I> generating the correct field */            
     m := d div 2;
     gens := [ ExtractBlock (I.t, 1, 1, m, m) : t in [1..Ngens (I)] ];
     resI := sub < MatrixAlgebra (k, m) | gens >;
     M := RModule (resI);
     isit, XX, e := IsAbsolutelyIrreducible (M);
     if isit then
         X := k.1 * Identity (resI);
         e := 1;
     else
         /* swap given <X> for one generating target <K> over GF(p) */
         EX := sub < Parent (XX) | XX >;
         p := Characteristic (k);
         f := Degree (k);
         facs := [ fac[1] : fac in Factorisation (e*f) ];
         count := 0;
         found := false;
         while (not found) and (count lt 200) do
	    count +:= 1;
	    X := Random (EX);
            if forall { i : i in [1..e*f-1] | X^(p^i) ne X } then
               found := true;
            end if;
         end while;
         assert found;
     end if;  
     mX := MinimalPolynomial (X);
     /* determine how its image is twisted in <J> */
     zero := RED!0;
     x := InsertBlock (zero, X, 1, 1);
     x0 := InsertBlock (zero, Identity (MatrixAlgebra (k, m)), 1, 1);
     y := x @ D`Star;
     Y := ExtractBlock (y, m+1, m+1, m, m);
     frob := -1;
     found := false;
     while (frob lt e * Degree (k)) and (not found) do
         frob +:= 1;
         if mX eq MinimalPolynomial (Y^(p^frob)) then
            found := true;
         end if;
     end while;
     
     if (not found) then
         "[Recognise Exchange]: failed to find suitable automorphism";
         return false, _, _, _;
     end if;

     /* construct the natural representation */
     n := m div e;
     z := x + (x @ D`Star);
     ms := KMatrixSpace (k, d, d);
     zIbas := [x0] cat [ x^f : f in [1..e-1] ];
     for i in [1..n^2-1] do
         assert exists (s){ t : t in [1..Ngens (I)] | 
                            not I.t in sub < ms | zIbas > };
         zIbas cat:= [ I.s * (z^f) : f in [0..e-1] ];
     end for;
     zJbas := [ (zIbas[i]) @ D`Star : i in [1..#zIbas] ];
     kgens := zIbas cat zJbas;

             /* change to nicer generators of <D> */
             A := sub < Generic (D) | kgens >;
             A`Star := D`Star;
             D := A;

     K := ext < k | mX >;
     V := VectorSpace (k, d);
     bas := [ (V.1) * z^t : t in [0..e-1] ];
     for i in [1..2*n-1] do
         assert exists (j){ k : k in [1..d] |
                     not V.k in sub < V | bas > };
         bas cat:= [ (V.j) * z^t : t in [0..e-1] ];
     end for;

     /* construct the generator for Aut(<K>) as matrix over <k> */
     AutK_vecs := [ EltseqWithBasis (K, k, [(K.1)^i : i in [0..e-1]], 
		   Frobenius ((K.1)^i, Degree (k))) : i in [0..e-1] ];
     AutK_action := MatrixAlgebra (k, e)!Matrix (AutK_vecs); 
     AutK_generator := DiagonalJoin (< AutK_action : i in [1..2*n] >);
     COB := MatrixAlgebra (k, d)!Matrix (bas);
     AutK_generator := COB^-1 * AutK_generator * COB;
     AutK := AutK_generator @ psi;

assert forall { i : i in [1..Ngens (S)] | AutK * S.i * AutK^-1 in S };
assert forall { i : i in [1..Ngens (S)] | 
   AutK * (S.i @ S`Star) * AutK^-1 eq (AutK * S.i * AutK^-1) @ S`Star }; 

     normaliserGenerators cat:= [ AutK ];
     normaliserOrder *:= e;

     /* construct the images of <kgens> over the larger field <K> */
     W := VectorSpaceWithBasis (bas);
     MA := MatrixAlgebra (K, 2*n);
     KIgens := [ ];
     for h in zIbas do
         hh := [];
         for j in [1..2*n] do
            v := W.(1+(j-1)*e) * h;
            c := Coordinates (W, v);
            vec := [ &+ [ c[(j-1)*e+t] * (K.1)^(t-1) : t in [1..e] ] : 
                                                   j in [1..2*n] ];
            hh cat:= vec;
         end for;
         Append (~KIgens, MA!hh);
     end for;

     q := p^frob;
     KJgens := [ ];
     for h in zJbas do
         hh := [];
         for j in [1..2*n] do
            v := W.(1+(j-1)*e) * h;
            c := Coordinates (W, v);
            vec := [ &+ [ c[(j-1)*e+t] * (K.1)^(q*(t-1)) : t in [1..e] ] : 
                                                       j in [1..2*n] ];
            hh cat:= vec;
         end for;
         Append (~KJgens, MA!hh);
     end for;

     NAT := sub < MA | KIgens cat KJgens >;

     /* construct inverse isomorphisms and induce star */
     DtoNAT := hom < D -> NAT | r :-> __AtoB (D, NAT, r) >;
     NATtoD := hom < NAT -> D | r :-> __BtoA (D, NAT, e, q, r) >;

     NAT`Star := hom < NAT -> NAT | r :-> ((r @ NATtoD) @ D`Star) @ DtoNAT >;

     /* update <phi> and <psi> and then work with <NAT> */
     phi := hom < S -> NAT | r :-> (r @ phi) @ DtoNAT >;
     psi := hom < NAT -> S | r :-> (r @ NATtoD) @ psi >;

     /* finally recognise the natural representation */
     R1gens := [ ExtractBlock (KIgens[i], 1, 1, n, n) : i in [1..#KIgens] ];
     R2gens := [ ExtractBlock (KJgens[i], n+1, n+1, n, n) : i in [1..#KJgens] ];
     S2gens := [ Transpose (R2gens[i]) : i in [1..#R2gens] ];
     R1 := sub < MatrixAlgebra (K, n) | R1gens >;
     R2 := sub < MatrixAlgebra (K, n) | R2gens >;
     S2 := sub < MatrixAlgebra (K, n) | S2gens >;
     M1 := RModule (R1);
     M2 := FrobeniusImage (RModule (R2), -frob);
     N2 :=  FrobeniusImage (RModule (S2), -frob);
     isit, C := IsIsomorphic (M1, N2);
     assert isit;
     C := DiagonalJoin (C, Identity (R1));
     Cinv := C^-1;

     STAN := MySimpleStarAlgebra ("exchange", 2*n, K : Frob := frob);
     NATtoSTAN := hom < NAT -> STAN | r :-> Cinv * r * C >;
     STANtoNAT := hom < STAN -> NAT | r :-> C * r * Cinv >;
       
     /* update <phi> and <psi> and assemble data structure */
     phi := hom < S -> STAN | r :-> (r @ phi) @ NATtoSTAN >;
     psi := hom < STAN -> S | r :-> (r @ STANtoNAT) @ psi >;

     normaliserOrder *:= STAN`StarAlgebraInfo`normaliserOrder;
//"order check:", normaliserOrder mod (#K - 1)^2 eq 0;
     normaliserOrder div:= (#K - 1)^2;
     STAN_normGens := STAN`StarAlgebraInfo`normaliserGenerators;
     conformalGenerators := [ x @ psi : x in STAN_normGens ];

assert forall { c : c in conformalGenerators |
  forall { i : i in [1..Ngens (S)] | c * (S.i) * c^-1 in S } };
assert forall { c : c in conformalGenerators |
  forall { i : i in [1..Ngens (S)] | c * (S.i @ S`Star) * c^-1 eq
           (c * S.i * c^-1) @ S`Star } };

     normaliserGenerators cat:= conformalGenerators;

     SSI_data`simpleParameters := STAN`StarSimpleInfo`simpleParameters;
     SSI_data`standardSimple := STAN;
     SSI_data`conformalGenerators := conformalGenerators;
     SSI_data`fieldAutoGenerator := AutK;
     SSI_data`centraliserGenerators := centraliserGenerators;
     SSI_data`standardIsomorphism := phi;
     SSI_data`standardInverse := psi;
     
     SAI_data`isSimple := true;
     SAI_data`isSemisimple := true;
     SAI_data`jacobsonRadical := sub < Generic (S) | S!0 >;
     SAI_data`taftComplement := S;
     SAI_data`srComponents := < S >;
     SAI_data`srDegrees := [ Degree (S) ];
     SAI_data`basicSimpleTypes := < "exchange" >;
     SAI_data`normaliserGenerators := normaliserGenerators;
     SAI_data`normaliserOrder := normaliserOrder;
     SAI_data`primitiveIdempotents :=
        [ x @ psi : x in STAN`StarAlgebraInfo`primitiveIdempotents ];
    
     S`StarAlgebraInfo := SAI_data;
     S`StarSimpleInfo := SSI_data;
     
return true, STAN, phi, psi;
end intrinsic;


