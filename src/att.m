/* 
    Copyright 2013--2017, Peter A. Brooksbank, James B. Wilson.
    Distributed under GNU GPLv3.
*/


declare attributes 
              AlgMat: 
                              IsBasis,
                          AlgebraInfo,
                                 Star,
                      StarAlgebraInfo,
                       StarSimpleInfo;

declare attributes
              AlgGrp:
                                 Star,
                      StarAlgebraInfo;
                       
declare attributes              
              GrpMat:
                  StructuralInformation;

declare verbose NormStar, 1;

declare verbose Isometry, 1;

declare verbose AdjointAlgebra, 1;
