/* 
    Copyright 2013--2017, Peter A. Brooksbank, James B. Wilson.
    Distributed under GNU GPLv3.
*/


   /*--- This file contains main intrinsics for package. ---*/

import "verify.m": IsIsometry, IsSimilarity;

import "prelims.m": PreimageUsingWordGroup;

import "form.m": BilinearForm, SesquilinearForm;


          /*--- isometries of arbitrary systems of forms ---*/
          

IsReflexiveForm := function (F)
  e := Degree (BaseRing (Parent (F)));
  if F eq Transpose (F) then
    return true;
  elif F eq -Transpose (F) then
    return true;
  elif (e mod 2 eq 0) and (F eq Transpose (FrobeniusImage (F, e div 2))) then
    return true;
  end if;
return false;
end function;


intrinsic IsometryGroup (S::SeqEnum :
  			    //Autos := [0 : i in [1..#S]],
                            Autos := [0 : i in [1..#Set (S)]],
			    DisplayStructure := false,
          Adjoint := 0
                        ) -> GrpMat

  { Find the group of isometries of the system of reflexive forms }

     /* attempted bug fix: avoid repetition */
     S := [ F : F in Set (S) ];

     require #S gt 0 : "argument 1 is empty";
     
     require #S eq #Autos : "arguments have unequal length";

     require forall { i : i in [1..#S] | 
                       Type (S[i]) eq AlgMatElt } :
        "elements of argument 1 are not matrices";
        
     require forall { i : i in [1..#S] |
                       IsReflexiveForm (S[i]) } :
        "elements of argument 1 do not represent reflexive forms"; 
     
     n := #S;
     MA := Parent (S[1]);
     k := BaseRing (MA);
     
     require Type (k) eq FldFin : 
        "Base ring of argument 1 is not a finite field.";
        
     require Characteristic (k) ne 2 : 
        "Base ring of argument 1 has characteristic 2.";
     
     d := Degree (MA);
     e := Degree (k);
     
     require forall { i : i in [2..n] | 
                      BaseRing (Parent (S[i])) eq k } :
        "Elements of argument 1 are not forms on a common module";
 
     require forall { i : i in [2..n] |
                      Degree (Parent (S[i])) eq d } :
        "Elements of argument 1 are not forms on a common module";
        
     require forall {f : f in Autos | (f eq 0) or (e mod f) eq 0} :
         "argument 2 is not a list of Frobenius exponents";

     /* deal with trivial case */
//     if (#S eq 1) then
//	 ISOM := IsometryGroup (S[1] : Auto := Autos[1]);
//         return ISOM;
//     end if;


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
//"(1)", Cputime (tt);

//tt := Cputime ();
     /* construct the adjoint algebra of <nForms> */
     if Type(Adjoint) eq RngIntElt then
        ADJ := AdjointAlgebra (nForms : Autos := Autos);
     else
        ADJ := Adjoint; // currently cannot compute the adjoint algebra of a degenerate system, so this shouldn't be too painful.
     end if;
//"(2)", Cputime (tt);

//tt := Cputime ();
     /* recognise the adjoint algebra */
     assert RecogniseStarAlgebra (ADJ);
//"(3)", Cputime (tt);

//tt := Cputime ();
     /* construct gens for the isometry group <nSigma> */
     gens := ADJ`StarAlgebraInfo`sharpGroupGenerators;
     ord := ADJ`StarAlgebraInfo`sharpGroupOrder;

     /* are we over the correct (input) field or over a subfield? */
     if #BaseRing (ADJ) lt #k then
         assert assigned ADJ`StarAlgebraInfo`mapToCorrectField;
         mtcf := ADJ`StarAlgebraInfo`mapToCorrectField;
         gens := [ GL (d-r, k)!(gens[t] @ mtcf) : t in [1..#gens] ];
     end if;
//"(4)", Cputime (tt);
 
//tt := Cputime ();
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
//"(5)", Cputime (tt);

//tt := Cputime ();
     ISOM := sub < GL (d, k) | gens >;

     /* final sanity check */ 
     assert forall {t: t in [1..Ngens (ISOM)] |
     forall {i: i in [1..#S] | IsIsometry (S[i], Autos[i], ISOM.t) }};


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

     p := Characteristic (k);
     f := Degree (k);

     exp := #ADJ`StarAlgebraInfo`alternatingRadical + f*r*(d-r);

     if DisplayStructure then
         "   G";
         for t in sgroups do
	    "   |  ", t[1],"(",t[2],",",t[3][1],"^",t[3][2],")";
            "   *";
	 end for;
         "   |  ", p,"^",exp,"   (unipotent radical)";
         "   1";
     end if;

     RF := recformat < order , facUROrder , simpleTypes >;
     SI_data := rec < RF | order := ord,
			   facUROrder := <p, exp>,
                           simpleTypes := sgroups
                     >;

     ISOM`StructuralInformation := SI_data;
     ISOM`Order := ord;
//"(6)", Cputime (tt);

return ISOM;

end intrinsic;


           /* ---- classical intersection ---- */

__my_determinant_map := function (X)
   return GL (1, BaseRing (X))![Determinant (X)];
end function;

__my_spinor_map := function (X, F)
   a := SpinorNorm (X, F);
   if a eq 0 then
      return Identity (GL (1, 3));
   else
      return -Identity (GL (1, 3));
   end if;
end function;

intrinsic ClassicalIntersection (S::SeqEnum : Forms := [], Autos := [] ) -> GrpMat

  { Find the intersection of a collection of classical groups defined
    on the same underlying module }

     require forall { G : G in S | Type (G) eq GrpMat } :
        "elements of argument are not matrix groups";
  
     k := BaseRing (S[1]);
     d := Degree (S[1]);
     
     require Characteristic (k) ne 2 : 
        "groups in argument are not defined over a finite field
         of odd characteristic";
         
     require forall { i : i in [2..#S] | BaseRing (S[i]) eq k } :
        "groups in argument are not defined on the same module";
  
     require forall { i : i in [2..#S] | Degree (S[i]) eq d } :
        "groups in argument are not defined on the same module"; 

     if #Forms eq 0 then
         /* find forms preserved by <grps> */
         Forms := [ ];
         Autos := [ ];
         for i in [1..#S] do
               X := S[i];
               flag, F := BilinearForm (X);
               if (not flag) then
                  flag, F := SesquilinearForm (X);
                  require flag : "argument is not a list of classical groups";
// added by PAB on 7/24/2020 as temp fix
assert Degree (k) mod 2 eq 0;
auto := Degree (k) div 2;
assert exists (a){ b : b in k | b ne 0 and Transpose (b*F) eq FrobeniusImage (b*F, auto) };
F := a * F;       
               else
                  auto := 0;
               end if;
               Append (~Forms, F);
               Append (~Autos, auto);
         end for;
     end if;

     /* find intersection of full isometry groups of these forms */
     ISOM := IsometryGroup (Forms : Autos := Autos, 
                                    DisplayStructure := false
                           );


         /*--- descend to the correct intersection ---*/

     /* first make sure we have the correct determinant */
     I := ISOM;
     D := GL (1, k);
     Idet_gens := [ __my_determinant_map (I.i) : i in [1..Ngens (I)]];
     Idet := sub < D | Idet_gens >;
     K := Idet;
     for i in [1..#S] do
         G := S[i];
         Gdet_gens := [ __my_determinant_map (G.j) : j in [1..Ngens (G)] ];
         Gdet := sub < D | Gdet_gens >;
         K meet:= Gdet;
      end for;
      if K ne Idet then
         J := PreimageUsingWordGroup (I, Idet, Idet_gens, K);
         J`StructuralInformation := I`StructuralInformation;
         J`StructuralInformation`order := 
               J`StructuralInformation`order div (#Idet div #K);
         I := J;
      end if;

      /* next impose individual spinor norm restrictions */
      D := GL (1, 3);
      for i in [1..#S] do
         G := S[i];
         F := Forms[i];
         if (Autos[i] eq 0) and (F eq Transpose (F)) then
            Isp_gens := [ __my_spinor_map (I.j, F) : j in [1..Ngens (I)] ];
            Isp := sub < D | Isp_gens >;
            Gsp_gens := [ __my_spinor_map (G.j, F): j in [1..Ngens (G)] ];
            Gsp := sub < D | Gsp_gens >;
            if not (Isp subset Gsp) then
               K := Isp meet Gsp;
               J := PreimageUsingWordGroup (I, Isp, Isp_gens, K);
               J`StructuralInformation := I`StructuralInformation;
               J`StructuralInformation`order := 
                     J`StructuralInformation`order div (#Isp div #K);
               I := J;
            end if;
         end if;
      end for;

return I;
end intrinsic;


__DerivedSubgroup_APPROX := function (G)
  X := [ (Random (G), Random (G)) : i in [1..5] ];
return sub < Generic (G) | X >;
end function;

/*
   ADDED BY PAB ON 7/22/2020.

   Notes: a basic version of the function we will perhaps eventually want.

   Given: a list of groups G, each of which preserves a sesquilinear form up
   to scalar multiple, and each of which also contains the full isometry 
   group preserving that form. (We will likely want to relax the latter 
   condition eventually.)

   Output: the intersection of the groups in the list.
*/

intrinsic ConformalIntersection (S::SeqEnum) -> GrpMat

  { Find the intersection of a collection of conformal classical groups. }

     require forall { G : G in S | Type (G) eq GrpMat } :
        "elements of argument are not matrix groups";
  
     k := BaseRing (S[1]);
     n := #S;
     d := Degree (S[1]);
     
     require Characteristic (k) ne 2 : 
        "groups in argument are not defined over a finite field
         of odd characteristic";
         
     require forall { i : i in [2..#S] | BaseRing (S[i]) eq k } :
        "groups in argument are not defined on the same module";
  
     require forall { i : i in [2..#S] | Degree (S[i]) eq d } :
        "groups in argument are not defined on the same module"; 
         
         /* 
            the hypothesis on the input ensures that the derived
            subgroup of each group in S preserves a unique form.
         */
         DS := [ __DerivedSubgroup_APPROX (X) : X in S ];  // change to DerivedSubgroupMonteCarlo
         Forms := [ ];
         for X in DS do
              flag, F := BilinearForm (X);
 //             require flag : "some group in the list does not preserve a unique form up to scalar";
              Append (~Forms, F);
         end for;
      
     /* 
        each group in S induces a subgroup of scalars on the 1-space spanned by its form;
        hence, the entire list S defines a subgroup of B := (k^*)^n;
        this is the "outer" group of pseudo-isometries we will try to lift
     */
     A, f := MultiplicativeGroup (k);
     B, i := DirectSum([ A : j in [1..n] ]);
     Y := [ ];
     for j in [1..n] do
          G := S[j];
          for s in [1..Ngens (G)] do
               M := G.s * Forms[j] * Transpose (G.s) * Forms[j]^-1;
               require IsScalar (M) : "some group in the list does not preserve a unique form up to scalar";
               Append (~Y, (M[1][1] @@ f) @ i[j]);
          end for;
     end for;
     U := sub < B | Y >;
     "proportion of all scalar lifts we must try:", #U / #B;
     "total:", #U;

     /* find intersection of full isometry subgroups of these groups */
     ISOM := IsometryGroup (Forms : DisplayStructure := false);

     L := [ ]; 
     /* try to lift outer pseudo-isometries */
     T := Tensor (Forms, 2, 1);
     for u in U do
          v := Eltseq (u);
          Fu := [ ((v[j] * A.1) @ f) * Forms[j] : j in [1..n] ];
          Tu := Tensor (Fu, 2, 1);
          isit, g := IsIsometric (T, Tu);
          if isit then
               assert forall { j : j in [1..n] | g * Forms[j] * Transpose (g) eq Fu[j] };
               Append (~L, g);
          end if;
     end for;

     H := sub < Generic (ISOM) | ISOM , L >;
     "index of isometry group in the intersection:", LMGOrder (H) div LMGOrder (ISOM);

return H;

end intrinsic;

// 9/22/2020
intrinsic ConformalUnitaryIntersection (S::SeqEnum) -> GrpMat

  { Find the intersection of a collection of conformal classical groups. }

     require forall { G : G in S | Type (G) eq GrpMat } :
        "elements of argument are not matrix groups";
  
     k := BaseRing (S[1]);
     n := #S;
     d := Degree (S[1]);
     
     require Characteristic (k) ne 2 : 
        "groups in argument are not defined over a finite field
         of odd characteristic";
         
     require forall { i : i in [2..#S] | BaseRing (S[i]) eq k } :
        "groups in argument are not defined on the same module";
  
     require forall { i : i in [2..#S] | Degree (S[i]) eq d } :
        "groups in argument are not defined on the same module"; 
         
         /* 
            the hypothesis on the input ensures that the derived
            subgroup of each group in S preserves a unique form.
         */
         DS := [ __DerivedSubgroup_APPROX (X) : X in S ];
         Forms := [ ];
         for X in DS do
              flag, F := SesquilinearForm (X);
 //             require flag : "some group in the list does not preserve a unique form up to scalar";
Append (~Forms, Transpose (F));
// N.B. For some reason SesquilinearForm is not quite 
// aligned with the usual Magma preservation of form
         end for;
      
     /* 
        each group in S induces a subgroup of scalars on the 1-space spanned by its form;
        hence, the entire list S defines a subgroup of B := (k^*)^n;
        this is the "outer" group of pseudo-isometries we will try to lift
     */
     A, f := MultiplicativeGroup (k);
     B, i := DirectSum([ A : j in [1..n] ]);
     Y := [ ];
     e := Degree (k) div 2;
     for j in [1..n] do
          G := S[j];
          for s in [1..Ngens (G)] do
               M := G.s * Forms[j] * FrobeniusImage (Transpose (G.s), e) * Forms[j]^-1;
               require IsScalar (M) : "some group in the list does not preserve a unique form up to scalar";
               Append (~Y, (M[1][1] @@ f) @ i[j]);
          end for;
     end for;
     U := sub < B | Y >;
     "proportion of all scalar lifts we must try:", #U / #B;
     "total:", #U;

     /* find intersection of full isometry subgroups of these groups */
     ISOM := IsometryGroup (Forms : DisplayStructure := false, Autos := [e : i in [1..n]]);
     ISOM := sub < Generic (ISOM) | [ FrobeniusImage (ISOM.i, e) : i in [1..Ngens (ISOM)] ] >;
     // action twisted again 
     assert forall { g : g in ISOM | 
             forall { F : F in Forms | g * F * FrobeniusImage (Transpose (g), e) eq F } };

/*
     L := [ ]; 
     T := Tensor (Forms, 2, 1);
     for u in U do
          v := Eltseq (u);
          Fu := [ ((v[j] * A.1) @ f) * Forms[j] : j in [1..n] ];
          Tu := Tensor (Fu, 2, 1);
          isit, g := IsIsometric (T, Tu);
          if isit then
               assert forall { j : j in [1..n] | g * Forms[j] * Transpose (g) eq Fu[j] };
               Append (~L, g);
          end if;
     end for;
     H := sub < Generic (ISOM) | ISOM , L >;
     "index of isometry group in the intersection:", LMGOrder (H) div LMGOrder (ISOM);
*/

H := ISOM;

return H;

end intrinsic;