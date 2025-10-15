% IPv6 header encoder helper for Duality MiniZinc models.
% Maps 8D unit-sum coordinates x[1..8] in 0..N to 8x 16-bit hextets.

int: N;                    % existing scale (e.g., 100)
array[1..8] of var 0..N: x;

% Derived 16-bit hextets from x (scale into 0..65535)
array[1..8] of var 0..65535: hextet;

constraint forall(i in 1..8)(
  hextet[i] = round( (x[i] * 65535.0) / (N + 0.0) )
);

% Optional: embed a Monster prime bitmask in the last hextet (low 16 bits).
% Provide P as set of Monster primes; map into a small hash/mod mask.
set of int: P;
var 0..65535: monster_mask;
constraint monster_mask =
  (sum(p in P)( p mod 65536 )) mod 65536;

% You can combine into a 128-bit conceptual value (hextets[1]..hextets[8]).
% Note: MiniZinc lacks native 128-bit; keep as hextets for output.

% Sample output annotations (if used standalone)
% solve satisfy;
% output [
%   "x=", show(x), "\n",
%   "hextet=", show(hextet), "\n",
%   "monster_mask=", show(monster_mask), "\n"
% ];
