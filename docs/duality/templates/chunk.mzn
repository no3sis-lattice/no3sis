% Template MiniZinc model for a chunk with 8D unit-sum manifold + Monster primes

% Parameters (templated)
int: N = {{SCALE_N}};  % sum(x[i]) = N (discrete unitary)
set of int: P = { {{MONSTER_PRIME_SET}} };  % subset of primes (2,3,5,7,11,13,17,19)

% Decision variables: 8D coordinates
array[1..8] of var 0..N: x;

% Unit-sum constraint
constraint sum(i in 1..8)(x[i]) = N;

% Domain-specific constraints injected here:
% {{CONSTRAINTS}}

% Optional objectives:
% {{OBJECTIVE}}

solve satisfy;
