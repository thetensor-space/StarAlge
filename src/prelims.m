/* 
    Copyright 2013--2017, Peter A. Brooksbank, James B. Wilson.
    Distributed under GNU GPLv3.
*/


    /*--- file contains useful miscellaneous functions ---*/


/* computes solutions to system Q.A + B.Q^t = 0 */
SolveSystem := function (A, B)
     n := Nrows (A);
     f := BaseRing (A);
     W := VectorSpace (f, n^2);
     mat := [];
     for i in [1..n] do
         for j in [1..n] do
            row := W!0;
            for k in [1..n] do
               row[(i-1)*n+k] := row[(i-1)*n+k] + A[k][j];
               row[(j-1)*n+k] := row[(j-1)*n+k] + B[i][k];
            end for;
            Append (~mat, row);
         end for;
     end for;
     mat := Matrix (mat);
     mat := Transpose (mat);
return Nullspace (mat);
end function;


/* return algebra induced by <alg> on invariant subspace <X> */
InducedAlgebra := function (alg, X)
    MA := MatrixAlgebra (BaseRing (alg), Dimension (X));
    gens := [ ];
    for i in [1..Ngens (alg)] do
       ims := [ ];
       for j in [1..Ngens (X)] do
          Append (~ims, Coordinates (X, X.j * alg.i));
       end for;
       Append (~gens, MA!Matrix (ims));
    end for; 
return sub < MA | gens >;
end function;


/* map on defining generators extends to iso <algA> -> <algB> */
AlgebraIsomorphism := function (algA, algB)
     MSA := KMatrixSpace (BaseRing (algA), Degree (algA), Degree (algA));
     MSB := KMatrixSpace (BaseRing (algB), Degree (algB), Degree (algB));
     spA := KMatrixSpaceWithBasis ([ MSA!(algA.i) : i in [1..Ngens (algA)] ]); 
     spB := KMatrixSpaceWithBasis ([ MSB!(algB.i) : i in [1..Ngens (algB)] ]); 
     mapAB := hom < algA -> algB | x :-> 
                   &+ [ c[i] * algB.i : i in [1..Ngens (algB)] ]
                   where c := Coordinates (spA, MSA!x) >;
     mapBA := hom < algB -> algA | x :-> 
                   &+ [ c[i] * algA.i : i in [1..Ngens (algA)] ]
                   where c := Coordinates (spB, MSB!x) >;              
return mapAB, mapBA;
end function;


/* analogue of "Eltseq" that allows one to specify basis */
EltseqWithBasis := function (K, k, bas, x)
     assert #bas eq (Degree (K) div Degree (k));
     W, g := VectorSpace (K, k);
     U := VectorSpaceWithBasis ([ bas[i] @ g : i in [1..#bas] ]);
return Coordinates (U, x @ g);
end function;


/* 
 given <T> acting irreducibly on its underlying module, return 
 inverse isomorphsisms from Env(<T>) to the isomorphic field.
 */
IsomorphismWithField := function (T)
     if T eq Identity (Parent (T)) then
         K := BaseRing (Parent (T));
         EnvT := sub < Parent (T) | T >;
         phi := hom < EnvT -> K | x :-> x[1][1] >;
         psi := hom < K -> EnvT | x :-> x * T >;
     else
         mT := MinimalPolynomial (T);
         assert IsIrreducible (mT);
         e := Degree (mT);
         k := BaseRing (Parent (T));
         d := Degree (Parent (T));
         K := ext < k | mT >;
         Kbas := [ (K.1)^i : i in [0..e-1] ];
         Tbas := [ T^i : i in [0..e-1] ];
         MS := KMatrixSpace (k, d, d);
         MS := KMatrixSpaceWithBasis ([ MS!(Tbas[i]) : i in [1..e] ]);
         EnvT := sub < Parent (T) | T >; 
         phi := hom < EnvT -> K | x :-> &+ [c[i] * Kbas[i] : i in [1..e]]
            where c := Coordinates (MS, MS!x) >;
         psi := hom < K -> EnvT | x :-> &+ [c[i] * Tbas[i] : i in [1..e]]
            where c := EltseqWithBasis (K, k, Kbas, x) >;
     end if;
return EnvT, K, phi, psi;
end function;


/* lifted from composition tree machinery */
__approximate_kernel := function (wdgrp, G, alpha, gamma, delta:
                     NumberRandom := 50, KernelRank := 25)
   P := Generic (G);
   proc := RandomProcess (wdgrp);
   kgens := [];
   for i in [1..NumberRandom] do
       wd := Random (proc);
       a := alpha (wd);
       d := delta (wd);
       c := gamma (a);
       e := delta (c);
       k := d * e^-1;
       Append (~kgens, k);
   end for;
   K := sub <P | kgens >;
   // "Rank of K is ", Ngens (K);
   return [NormalSubgroupRandomElement (G, K) : i in [1..KernelRank]];
end function;


/* 
   <G> = group
   <H> = homomorphic image of <G>
   <Hgens> = images of defining generators of <G>
   <K> = subgroup of H;  
   return preimage of <K> in <G>
*/
PreimageUsingWordGroup := function (G, H, Hgens, K:
                                    NumberRandom := 50, KernelRank := 10)
     P := Generic (G);
     B := SLPGroup (#Hgens);
     tau := InverseWordMap (H);
     index := [ Position (Hgens, H.i) : i in [1..Ngens (H)] ];
     S := Image (tau);
     eta := hom < S -> B | [ B.i : i in index ] >;
     gamma := tau * eta;
     delta := hom < B -> G | [ G.i : i in [1..Ngens (G)] ] >;
     alpha := hom < B -> H | Hgens >;
     ker := __approximate_kernel (B, G, alpha, gamma, delta:
                  NumberRandom := NumberRandom, KernelRank := KernelRank);
     KgensB := [gamma (K.i) : i in [1..Ngens (K)]];
     KgensG := [delta (KgensB[i]) : i in [1..#KgensB]];
return sub < P | ker, KgensG >;
end function;


/* sets up record formats for the two main data structures we use */
__RF_SETUP := function (string)

     if (string eq "algebra") then

         return recformat <            isSimple, 
                                   isSemisimple, 
                                jacobsonRadical, 
                                 taftComplement, 
			       transitionMatrix,
			              srDegrees,
                                   srComponents,
                             alternatingRadical,
                               basicSimpleTypes, 
                                sharpGroupOrder, 
			   sharpGroupGenerators,
				normaliserOrder,
			   normaliserGenerators,
                           primitiveIdempotents,
                              mapToCorrectField
                          >;

     elif (string eq "simple") then

         return recformat < simpleParameters, 
                              standardSimple, 
reflexiveForm,
                         standardIsomorphism, 
			     standardInverse,
			          sharpGroup,
			     sharpGroupOrder,
			 conformalGroupOrder,
			 conformalGenerators,
			  fieldAutoGenerator,
                       centraliserGenerators
                          >;

     elif (string eq "grpalg") then

         return recformat <        isSimple, 
                               isSemisimple, 
                            jacobsonRadical,
                             taftComplement, 
                           simpleParameters
                          >;

     else

         return false;

     end if;

end function;

/* Determine positions of a basis for space spanned by given vectors */
IdentifyBasis := function (Q)
     U := Parent (Q[1]);
     flag := exists (i){ j : j in [1..#Q] | Q[j] ne U!0 };
     if not flag then
         return [];
     end if;
     positions := [i];
     remaining := [1..#Q];
     Remove (~remaining, i);
     extends := true;
     while extends do
         W := VectorSpaceWithBasis ([Q[c] : c in positions]);
         extends := exists (j){ i : i in [1..#remaining] | 
                                    not Q[remaining[i]] in W };
         if extends then
             Append (~positions, remaining[j]);
             Remove (~remaining, j);
         end if;
     end while;
return positions;
end function;


/*
   Has the functionality of the GAP function of the same name.
   Maybe this already exists in Magma but I could not find it.
*/
Collected := function (L)
     dist := Set (L);
return [ [ x , #{ i : i in [1..#L] | L[i] eq x } ] : x in dist ];
end function;



/* Added 5/24/16 by JM and JBW to compute Sym and Alt faster. */
/*
	XA - BY = 0

	A is s x b x c, 
	B is a x t x c

 */
/*__SymAlt := function( forms )
	c := #forms;	
	a := Nrows(forms[1]);
	b := Ncols(forms[1]);
	K := BaseRing(forms[1]);
	s := Nrows(forms[1]);
	t := Ncols(forms[1]);

	A := forms[1];
	for i in [2..c] do
		A := HorizontalJoin(A, forms[i]);
	end for;

	// echelonize the columns of A, storing the transform.
	// magma only does row-echelon (even though it only does right nullspace) grumble.
	temp := Transpose(A);
	temp, T := EchelonForm(temp);
	r := Rank(temp);
	// copy the content left over
	temp := ExtractBlock( temp, 1,1, r, Ncols(temp) );
	A := Transpose(temp);
	T := Transpose(T);
	delete temp;
		
	//mat := ZeroMatrix( K, a*s+t*b, a*b*c );
	// PENDING: it makes no sense to make this matrix, should just
	// store A and back solve iteratively.
	m1 := ZeroMatrix(K, s*a, r*a );
	for i in [1..a] do
		InsertBlock(~m1, A, s*(i-1)+1, r*(i-1)+1 );
	end for;

	delete A;

	slicedforms := [ [ ExtractBlock(-Transpose(B), 1, i, t, 1) : i in [1..a]] : B in forms ];
	m2 := ZeroMatrix(K, t*b, r*a);
	m3 := ZeroMatrix(K, t*b, a*b*c-r*a);
	for i in [1..a] do
		// Build the block blow the A's but hit it with the echelon transform.
		Z := ZeroMatrix(K, t*b, b*c);
		for j in [1..c] do
			for k in [1..b] do
				InsertBlock(~Z, slicedforms[j][i], t*(k-1)+1, b*(j-1)+k );
			end for;
		end for;
		Z := Z*T;
		// Partition along pivot lines and shuffle into echelon form.
		Z0 := ExtractBlock( Z, 1, 1, t*b, r );
		InsertBlock(~m2, Z0, 1, r*(i-1)+1 );

		Z1 := ExtractBlock( Z, 1, r+1, t*b, b*c-r);
		InsertBlock(~m3, Z1, 1, (c*b-r)*(i-1)+1 );
	end for;
	delete slicedforms;
	
	// Now solve.
	Sym := Nullspace(HorizontalJoin(m1+m2,m3));
	Alt := Nullspace(HorizontalJoin(m1-m2,m3));
	return [Matrix(K,a,s,Eltseq(x)) : x in Basis(Sym)], [Matrix(K,t,b,Eltseq(x)) : x in Basis(Alt)];
end function;*/

__SymAlt := function( forms )
	c := #forms;	
	a := Nrows(forms[1]);
  assert Ncols(forms[1]) eq a;
	K := BaseRing(forms[1]);
  T := Tensor(forms,2,1);
 
  A := ZeroMatrix(K,a^2,a^2*c);;
  Fa := Foliation(T,2);
  ipos := 1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock(~A,Fa,ipos,jpos);
    ipos +:= a;
    jpos +:= a*c;
  end for;
  delete Fa;

  B := ZeroMatrix(K,a^2,a^2*c);
  Fb := Transpose(Foliation(T,1));
  Fb_blocks := [* Transpose(Matrix(Fb[(i-1)*c+1..i*c])) : i in [1..a] *];
  delete Fb;
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    for j in [1..a] do
      InsertBlock(~B,Fb_blocks[i],ipos,jpos);
      ipos +:= a;
      jpos +:= c;
    end for;
  end for;
  delete Fb_blocks;
  
  alt := Nullspace(A+B);
  sym := Nullspace(A-B);
  return [Matrix(K,a,a,Eltseq(x)) : x in Basis(sym)], [Matrix(K,a,a,Eltseq(x)) : x in Basis(alt)];
end function;
