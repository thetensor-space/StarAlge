 /*--- Compute Lie algebra of derivations of system of forms ---*/

__block_diagonal := function (v, degrees)
     F := BaseRing (v);
     sqdegs := [ n^2 : n in degrees ];
     assert Degree (v) eq &+ sqdegs;
     mat := MatrixAlgebra (F, degrees[1])![ v[j] : j in [1..sqdegs[1]] ];
     start := sqdegs[1];
     for i in [2..#degrees] do
         Q := [ v[ start + j ] : j in [1..sqdegs[i]] ];
         mat := DiagonalJoin (mat, MatrixAlgebra (F, degrees[i])!Q);
         start +:= sqdegs[i];
     end for;
return mat;
end function;


__default_der := function (Forms)

     n := #Forms;
     e := Degree (Forms[1][1]);
     F := BaseRing (Forms[1][1]);
     X := VectorSpace (F, n^2 + e^2);

     mat := [];
     for i in [1..n] do
         for j in [1..n] do
            for k in [1..e] do
               row := X!0;
               for x in [1..n] do
	          row[ (i-1)*n + x ] +:= Forms[x][j][k];
               end for;
               for y in [1..n] do
	          row[ (j-1)*n + y ] +:= Forms[i][y][k];
               end for;
               for l in [1..e] do
	          row[ n^2 + (l-1)*e + k ] -:= Forms[i][j][l];
               end for;
               Append (~mat, row);
            end for;
         end for;
     end for; 

     mat := Transpose (Matrix (mat));
     sol := Nullspace (mat);
     basis := [ __block_diagonal (sol.i, [n, e]) : i in [1..Ngens (sol)] ];
     MS := KMatrixSpace (F, n + e, n + e);
     
     DER := sub < MS | [ MS!b : b in basis ] >;
     
/* sanity check */
OUT := [ ExtractBlock (DER.i, 1, 1, n, n) : i in [1..Ngens (DER)] ];
IN := [ ExtractBlock (DER.i, n+1, n+1, e, e) : i in [1..Ngens (DER)] ];
for i in [1..#Forms] do
for j in [1..#OUT] do
f := IN[j];
g := OUT[j];
//assert f * Forms[i] + Forms[i] * Transpose (f) eq &+ [ g[i][l] * Forms[l] : l in [1..n] ];
end for;
end for;

return DER;

end function;

