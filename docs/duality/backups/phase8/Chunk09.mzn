% Template MiniZinc model for a chunk with 8D unit-sum manifold + Monster primes

% Parameters (templated)
int: N = 100;  % sum(x[i]) = N (discrete unitary)
set of int: P = { 2, 3, 5, 7, 11, 13, 17, 19 };  % subset of primes (2,3,5,7,11,13,17,19)

% Decision variables: 8D coordinates
array[1..8] of var 0..N: x;

% Unit-sum constraint
constraint sum(i in 1..8)(x[i]) = N;

% Domain-specific constraints injected here:
% constraint: chunk_09_exists
constraint true;
% constraint: proof_required
constraint true;
% constraint: bridge_minimum
constraint x[1] + x[2] >= 10;
% constraint: bridge_balance
constraint abs(x[1] - x[2]) <= 5;
% constraint: bridge_modest
constraint sum(i in 1..3)(x[i]) <= 40;

% Optional objectives:
% none

solve satisfy;
