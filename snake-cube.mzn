% solve a cube-packing snake game

include "all_different.mzn";
include "inverse.mzn";
include "value_precede.mzn";
include "value_precede_chain.mzn";


int: nSegments = 17;
set of int: SEGMENT = 1..nSegments;
array[SEGMENT,1..2] of CUBE: segments = [|1,3|3,5|5,7|7,9|9,10|10,11|11,12|12,14|14,16|16,17|17,18|18,20|20,21|21,23|23,24|24,25|25,27|];
array[CUBE] of SEGMENT: segofcube = [ min(s in SEGMENT where segments[s,2] >= c)(s) | c in CUBE ];

set of int: X = 0..2;
set of int: Y = 0..2;
set of int: Z = 0..2;
set of int: CUBE = 1..27;
set of int: POS = 1..27;
enum DIR = { XP, XN, YP, YN, ZP, ZN };

array[POS] of var CUBE: cubes;
array[CUBE] of var POS: positions;
array[SEGMENT] of var DIR: directions;

constraint all_different(cubes);
constraint inverse(cubes,positions);

array[POS] of X: xs = [  (p - 1)        mod 3 | p in POS ];
array[POS] of Y: ys = [ ((p - 1) div 3) mod 3 | p in POS ];
array[POS] of Z: zs = [ ((p - 1) div 9) mod 3 | p in POS ];
constraint forall(x in X, y in Y, z in Z)(
  let { POS: pos = 1 + x + 3*y + 9*z } in
  xs[pos] = x /\
  ys[pos] = y /\
  zs[pos] = z
);

predicate samePos(CUBE: c0, CUBE: c1, array[POS] of int: proj) =
   proj[positions[c0]] = proj[positions[c1]];

predicate samePos(array[int] of CUBE: cubes, array[POS] of int: proj) =
   forall(c0, c1 in cubes where c0 < c1)(samePos(c0,c1,proj));

predicate along(array[int] of CUBE: cubes, array[POS] of int: proj) =
  let { CUBE: c0 = cubes[1]} in
  forall(c1 in cubes where c1 > c0)(abs(proj[positions[c0]] - proj[positions[c1]]) = c1 - c0);

predicate direction(SEGMENT: s, array[POS] of int: proj, DIR: dp, DIR: dn) =
  (proj[positions[segments[s,1]]] < proj[positions[segments[s,2]]] /\ directions[s] = dp)
  \/ (proj[positions[segments[s,1]]] > proj[positions[segments[s,2]]] /\ directions[s] = dn);
  
predicate rotateX(array[int] of CUBE: cubes) = along(cubes, xs)   /\ samePos(cubes, ys) /\ samePos(cubes, zs);
predicate rotateY(array[int] of CUBE: cubes) = samePos(cubes, xs) /\ along(cubes, ys)   /\ samePos(cubes, zs);
predicate rotateZ(array[int] of CUBE: cubes) = samePos(cubes, xs) /\ samePos(cubes, ys) /\ along(cubes, zs);

predicate straight(SEGMENT: s) = 
   let {CUBE: c0 = segments[s,1]; CUBE: c1 = segments[s,2]}
   in
   assert(c0 < c1, "invalid segment of non-increasing cube numbers",
          (rotateX(c0..c1) /\ direction(s, xs, XP, XN))
       \/ (rotateY(c0..c1) /\ direction(s, ys, YP, YN))
       \/ (rotateZ(c0..c1) /\ direction(s, zs, ZP, ZN))
   );

constraint forall(s in SEGMENT)(straight(s));

constraint value_precede(XP,XN, directions);
constraint value_precede(YP,YN, directions);
constraint value_precede(ZP,ZN, directions);
constraint value_precede_chain([XP,YP,ZP], directions);

predicate toto = true;


ann: s1 = seq_search(
  [ int_search(sort_by(directions,[segments[s,1] - segments[s,2]|s in SEGMENT]), input_order, indomain_min)
  ]);

ann: s2 = seq_search(
  [ int_search(positions, input_order, indomain_min)
  ]);

% solve satisfy;
solve :: s2 satisfy;

output [ show_int(2,c) ++ " " ++ show_int(2,27-c) ++ " " ++ show_int(2,segofcube[c]) ++
  " => \(directions[segofcube[c]]): x=\(xs[positions[c]]),y=\(ys[positions[c]]),z=\(zs[positions[c]])\n" | c in CUBE]
 