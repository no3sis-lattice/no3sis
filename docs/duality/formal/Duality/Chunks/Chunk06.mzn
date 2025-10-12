% Template MiniZinc model for a chunk with 8D unit-sum manifold + Monster primes

% Parameters (templated)
int: N = 100;  % sum(x[i]) = N (discrete unitary)
set of int: P = { 2, 3, 5, 7, 11, 13, 17, 19 };  % subset of primes (2,3,5,7,11,13,17,19)

% Decision variables: 8D coordinates
array[1..8] of var 0..N: x;

% Unit-sum constraint
constraint sum(i in 1..8)(x[i]) = N;

% Domain-specific constraints injected here:
% constraint: chunk_06_exists
constraint true;
% constraint: proof_required
constraint true;
% constraint: external_min_viable
constraint x[1] + x[2] + x[3] >= 30;
% constraint: external_reactive_bias
constraint sum(i in 1..4)(x[i]) >= sum(i in 5..8)(x[i]);
% constraint: external_min_per_layer
constraint forall(i in 1..4)(x[i] >= 3);

% Optional objectives:
% none

solve satisfy;
