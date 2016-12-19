wedge := function (u, v)
     n := Degree (Parent (u));
     k := BaseRing (Parent (u));
     d := Binomial (n, 2);
     W := VectorSpace (k, d);
     uwv := W!0;
     pos := 1;
     for i in [1..n] do
         for j in [1..i-1] do
            uwv[pos] := u[i]*v[j] - v[i]*u[j];
            pos +:= 1;
         end for;
     end for;
return uwv;
end function;
  

p := 3;
k := GF (p);
d := 7;

gl := GL (d, k);
ma := MatrixAlgebra (k, d);

x1 := Identity (ma);
x1[2][2] := -1;
x1[3][3] := -1;
x1[5][5] := -1;
x1[6][6] := -1;

x2 := ma![0,0,1,0,0,0,0,
          2,0,1,0,0,2,0,
          0,0,0,0,0,1,0,
          0,0,0,2,0,1,0,
          0,2,0,1,0,1,2,
          0,0,0,0,0,0,1,
          0,0,0,0,1,0,1];

y1 := gl!x1;
y2 := gl!x2;

G2 := sub < gl | y1, y2 >;

MatGrpToSystem := function (G)

     d := Degree (G);
     k := BaseRing (G);

     /* construct the action of <G> on the exterior square */
     EG, phi := ExteriorSquare (G);
     dE := Degree (EG);

     /* find the maximal submodules of the <EG>-module */
     M := GModule (EG);
     maxes := MaximalSubmodules (M);
     if not exists (N){ X : X in maxes | 
                            dE - Dimension (X) eq d } then
         return false;
     end if;

     V := VectorSpace (k, d);
     
     /* use <N> to form a bimap <V> x <V> -> <V> */
     
     W, f := M / N;
     S := [ ma!0 : i in [1..d] ];
     for i in [1..d] do
         for j in [1..d] do
            w := wedge (V.i, V.j) @ f;
            for s in [1..d] do
               S[s][i][j] := w[s];
            end for;
         end for;
     end for;
  
return S;

end function;


/*--- Steve's generators for G_2(3) ---*/
  
p := 3;
k := GF (p);
d := 7;
gl := GL (d, k);
ma := MatrixAlgebra (k, d);
x1 := Identity (ma);
x1[2][2] := -1;
x1[3][3] := -1;
x1[5][5] := -1;
x1[6][6] := -1;
x2 := ma![0,0,1,0,0,0,0,
          -1,0,1,0,0,-1,0,
          0,0,0,0,0,1,0,
          0,0,0,-1,0,1,0,
          0,-1,0,1,0,1,-1,
          0,0,0,0,0,0,1,
          0,0,0,0,1,0,1];
y1 := gl!x1;
y2 := gl!x2;
G2 := sub < gl | y1, y2 >;


/*--- system of forms obtained from Lie algebra g_2 ---*/

p := 5;
k := GF (p);
d := 7;
ma := MatrixAlgebra (k, d);
S := [ ma!0 : i in [1..d] ];
S[1][2][4] := 1; S[1][4][2] := -1;
S[1][3][7] := 1; S[1][7][3] := -1;
S[1][5][6] := 1; S[1][6][5] := -1;
S[2][1][4] := -1; S[2][4][2] := 1;
S[2][3][5] := 1; S[2][5][3] := -1;
S[2][6][7] := 1; S[2][7][6] := -1;
S[3][1][7] := -1; S[3][7][1] := 1;
S[3][2][5] := -1; S[3][5][2] := 1;
S[3][4][6] := 1; S[3][6][4] := -1;
S[4][1][2] := 1; S[4][2][1] := -1;
S[4][3][6] := -1; S[4][6][3] := 1;
S[4][5][7] := 1; S[4][7][5] := -1;
S[5][1][6] := -1; S[5][6][1] := 1;
S[5][2][3] := 1; S[5][3][2] := -1;
S[5][4][7] := -1; S[5][7][4] := 1;
S[6][1][5] := 1; S[6][5][1] := -1;
S[6][2][7] := -1; S[6][7][2] := 1;
S[6][3][4] := 1; S[6][4][3] := -1;
S[7][1][3] := 1; S[7][3][1] := -1;
S[7][2][6] := 1; S[7][6][2] := -1;
S[7][4][5] := 1; S[7][5][4] := -1;

T := [ X - Transpose (X) : X in S ];



tensor := function (u, v)
     s := Degree (Parent (u));
     t := Degree (Parent (v));
     k := BaseRing (Parent (u));
     W := VectorSpace (k, s*t);
     utv := W!0;
     for i in [1..s] do
         for j in [1..t] do
            utv[t*(i-1)+j] := u[i]*v[j];
         end for;
     end for;
return utv;
end function;


TensorBimap := function (X)

EndU := Parent (X[1][1]);
EndV := Parent (X[1][2]);
s := Degree (EndU);
t := Degree (EndV);
k := BaseRing (EndU);

U := VectorSpace (k, s);
V := VectorSpace (k, t);

UtenV := VectorSpace (k, s*t);

Xbas := [ ];
for x in X do
  for i in [1..s] do
    for j in [1..t] do
  Append (~Xbas, tensor (U.i * x[1], V.j) - tensor (U.i, V.j * x[2]));    
    end for;
  end for;
end for;
  
tensorX, phi := UtenV / sub < UtenV | Xbas >;

n := Dimension (tensorX);

S := [ KMatrixSpace (k, s, t)!0 : i in [1..n] ];
for i in [1..s] do
  for j in [1..t] do
    uitvj := Vector (tensor (U.i, V.j) @ phi);
    for z in [1..n] do
      S[z][i][j] := uitvj[z];
    end for;
  end for;
end for;
  
  return S;
   
  end function;
  
EllipticBimap := function (p)

MA := MatrixAlgebra (GF (p), 6);
S := [ MA!0 : i in [1,2,3] ];

J := MatrixAlgebra (GF (p), 2)![0,1,-1,0];

InsertBlock (~S[1], J, 1, 1);
InsertBlock (~S[1], J, 3, 3);

InsertBlock (~S[2], J, 1, 3);
InsertBlock (~S[2], J, 3, 1);
InsertBlock (~S[2], J, 5, 5);

InsertBlock (~S[3], J, 1, 5);
InsertBlock (~S[3], J, 5, 1);

return (S);


end function;

comm := function (x, y)
return x*y - y*x;
end function;
  
  


