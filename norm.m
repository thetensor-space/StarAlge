/* 
   contains the function to compute N^*(<ADJ>), which
   may be used as an overgroup to the stabiliser of an
   arbitrary system of alternating forms.
*/

intrinsic NormStar (S::SeqEnum : Autos := [ 0 : i in [1..#S] ]) -> GrpMat

  { If A is the algebra of adjoints of the system S, find the 
    group that normalises A and commutes with the involution on A.}

     require #S gt 0 : "argument 1 is empty.";
     
     require #S eq #Autos : "arguments have unequal length.";

     require forall { i : i in [1..#S] | Type (S[i]) eq AlgMatElt } :
        "elements of argument 1 are not forms";

     n := #S;
     MA := Parent (S[1]);
     k := BaseRing (MA);
     
     require Type (k) eq FldFin : 
        "Base ring of argument 1 is not a finite field.";

     require Characteristic (k) ne 2 : 
        "Base ring of argument 1 has characteristic 2.";     

     d := Degree (MA);
     e := Degree (k);
     
     require forall { i : i in [2..n] | BaseRing (Parent (S[i])) eq k } :
        "Elements of argument 1 are not forms on a common module"; 

     require forall { i : i in [2..n] | Degree (Parent (S[i])) eq d } :
        "Elements of argument 1 are not forms on a common module";
        
     require forall {f : f in Autos | (f eq 0) or (e mod f) eq 0} :
          "argument 2 is not a list of Frobenius exponents";

     /* deal with trivial case */
     if (#S eq 1) then
	 NORM := SimilarityGroup (S[1] : Auto := Autos[1]);
         return NORM;
     end if;


         /*--- find the isometry group via the adjoint algebra ---*/
       
     /* reduce to the nondegenerate case */
     rad := &meet [ Nullspace (FrobeniusImage (S[i], Autos[i])) : 
                    i in [1..#S] ];
     r := Dimension (rad);
     if r gt 0 then
         comp := Complement (Generic (rad), rad);
         C := GL (d, k)!Matrix (Basis (comp) cat Basis (rad));
         nForms := [ ];
         for i in [1..n] do
            FC := FrobeniusImage (C, Autos[i]) * S[i] * Transpose (C);
	    F := ExtractBlock (FC, 1, 1, d-r, d-r);
            Append (~nForms, F);
	 end for;
     else
         nForms := S;
     end if;


     /* construct the adjoint algebra of <nForms> */
     ADJ := AdjointAlgebra (nForms : Autos := Autos);

     /* recognise the adjoint algebra */
     assert RecogniseStarAlgebra (ADJ);

     /* extract normaliser gens for <ADJ> */
     gens := ADJ`StarAlgebraInfo`normaliserGenerators;
     ord := ADJ`StarAlgebraInfo`normaliserOrder;

     /* are we over the correct (input) field or over a subfield? */

     if #BaseRing (ADJ) ne #k then
        error "adjustment needed for field blow-up: not implemented yet";
     end if;

     /*
     if #BaseRing (ADJ) lt #k then
         assert assigned ADJ`StarAlgebraInfo`mapToCorrectField;
         mtcf := ADJ`StarAlgebraInfo`mapToCorrectField;
         gens := [ GL (d-r, k)!(gens[t] @ mtcf) : t in [1..#gens] ];
     end if;
     */ 

     /* add in generators for centraliser of <ADJ> in GL */

     /* commented out 5/5/2011: already accounted for within <gens> */

/*
CENT := Centraliser (Generic (ADJ), ADJ);
isit, U, Uord := UnitGroup (CENT);
assert isit;
ord *:= Uord; 
gens cat:= [ U.i : i in [1..Ngens (U)] ];
*/

     /* make necessary adjustments in the case of a nontrivial radical */
     if (r gt 0) then
 
	 /* embed the generators from <ADJ> */
         ngens := [ ];
         for t in [1..#gens] do
            x := Identity (GL (d, k));
            InsertBlock (~x, gens[t], 1, 1);
            Append (~ngens, x);
         end for;

         /* add in GL(r,k) generators */
         gl_gens := [ GL (r, k).i : i in [1..Ngens (GL (r, k))] ];
         for i in [1..#gl_gens] do
            x := Identity (GL (d, k));
            InsertBlock (~x, gl_gens[i], d-r+1, d-r+1);
            Append (~ngens, x);
         end for;
         ord *:= #GL (r, k);

         /* to be safe, add in all unipotent generators */
         for i in [1..d-r] do
            for j in [d-r+1..d] do
               x := Identity (MatrixAlgebra (k, d));
               x[i][j] := 1;
               Append (~ngens, GL (d, k)!x);
	    end for;
         end for;
         ord *:= (#k)^(r*(d-r));

         /* conjugate back */
         gens := [ C^-1 * ngens[i] * C : i in [1..#ngens] ];

     end if;

     NORM := sub < GL (d, k) | gens >;

     /* get simple types */
     stypes := [ S`StarSimpleInfo`simpleParameters : 
                 S in ADJ`StarAlgebraInfo`srComponents ];

     /* convert to group notation */
     if (r gt 0) then
         sgroups := [ < "GL" , r , [Characteristic (k), Degree (k)] > ];
     else
         sgroups := [ ];
     end if;
     for t in stypes do
         n := t[2];
         q := Factorization (t[3])[1];
         if t[1] eq "symplectic" then
            X := "Sp";
         elif t[1] eq "unitary" then
            X := "GU";
            q[2] := q[2] div 2;
         elif t[1] eq "orthogonalcircle" then
            X := "GO";
         elif t[1] eq "orthogonalminus" then
            X := "GOMinus";
         elif t[1] eq "orthogonalplus" then
            X := "GOPlus";
         else
            X := "GL";
            n := n div 2;
         end if;
         Append (~sgroups, <X, n, [q[1],q[2]]>);
     end for;

     NORM`Order := ord;

     index := ord div ADJ`StarAlgebraInfo`sharpGroupOrder;
     max_index:=#GL (d, k) div ADJ`StarAlgebraInfo`sharpGroupOrder;
		vprint NormStar, 1 : "[N : I] =", index, 
			"(", Ceiling(Log(2,index)), "/", Ceiling(Log(2,max_index)), "bits)";

return NORM;

end intrinsic;
