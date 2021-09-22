/* 
    Some test code for characteristic 2 isometry
*/


// test of vector stabilizer subroutine
k := 2;
K := GF (2^k);
RUNS := 10;

for i in [1..RUNS] do
    d := Random ([4..10]);
    r := Random ([4..d]);
"d =", d, "   r =", r;
    X := RandomSymmetricMatrix (K, d, r);
    V := VectorSpace (K, d, X);
    v := Random (V);
    H := VectorStabilizer (V, v);
end for;