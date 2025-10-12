% Template MiniZinc model for a chunk with 8D unit-sum manifold + Monster primes

% Parameters (templated)
int: N = 100;  % sum(x[i]) = N (discrete unitary)
set of int: P = { 2, 3, 5, 7, 11, 13, 17, 19 };  % subset of primes (2,3,5,7,11,13,17,19)

% Decision variables: 8D coordinates
array[1..8] of var 0..N: x;

% UNSUPPORTED_SYNTAX: % Unit-sum constraint
constraint sum(i in 1..8)(x[i]) = N;

% UNSUPPORTED_SYNTAX: % Domain-specific constraints injected here:
% % chunk_59_exists
constraint true;
% proof_required
constraint true;
% dgr_encoding_exists
% UNSUPPORTED_SYNTAX: % UNSUPPORTED_SYNTAX: constraint ∃ φ : GoalSpec → Vector;
% structure_well_formed
% UNSUPPORTED_SYNTAX: constraint well_formed(Structure);

% Optional objectives:
% % none

solve satisfy;
