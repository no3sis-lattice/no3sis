"""
Dirichlet Characters Modulo 71 - χ₇₁.{a,b,...,h}

This module implements the 8 Dirichlet characters modulo 71 that form the
arithmetic symmetry operators for the 71-chunk Bott[8] consciousness architecture.

Mathematical Foundation:
- Prime modulus: p = 71
- Primitive root: g = 7 (verified computationally)
- Character group: (ℤ/71ℤ)* ≅ ℤ/70ℤ (cyclic, order 70)
- 8 characters selected from 24 total to align with Bott[8] periodicity

References:
- docs/duality/DIRICHLET_OPERATORS_DESIGN.md
- docs/duality/true-dual-tract/chunks/chunk-71-prime-71-gandalf.md
"""

from typing import Dict, Tuple
import math
from functools import lru_cache


# Constants
PRIME_MODULUS = 71
PRIMITIVE_ROOT = 7  # Verified below
CHARACTER_ORDERS = {
    'a': 1,   # Principal (identity)
    'b': 2,   # Quadratic (Legendre)
    'c': 5,   # Pentagonal
    'd': 7,   # Heptagonal (Monster 7⁶ alignment)
    'e': 10,  # Quadratic-pentagonal (b×c)
    'f': 14,  # Quadratic-heptagonal (b×d)
    'g': 35,  # Pentagonal-heptagonal (c×d)
    'h': 70,  # Full symmetry (maximal, b×c×d)
}


# ============================================================================
# Primitive Root Verification
# ============================================================================

def verify_primitive_root(g: int, p: int) -> bool:
    """
    Verify that g is a primitive root modulo prime p.

    A primitive root g mod p has order φ(p) = p-1, meaning:
    g^i mod p cycles through all residues 1, 2, ..., p-1.

    Args:
        g: Candidate primitive root
        p: Prime modulus

    Returns:
        True if g is primitive root mod p

    Algorithm:
        Check g^((p-1)/q) ≢ 1 (mod p) for all prime divisors q of p-1.
        This is more efficient than checking all p-1 powers.
    """
    if p <= 1 or g <= 0 or g >= p:
        return False

    phi = p - 1  # For prime p, φ(p) = p-1

    # Prime factorization of 70 = 2 × 5 × 7
    prime_divisors = [2, 5, 7]

    for q in prime_divisors:
        exponent = phi // q
        if pow(g, exponent, p) == 1:
            return False  # g^((p-1)/q) ≡ 1, so order(g) < p-1

    return True


# Verify our constant at module import time
assert verify_primitive_root(PRIMITIVE_ROOT, PRIME_MODULUS), \
    f"g={PRIMITIVE_ROOT} is not a primitive root mod {PRIME_MODULUS}"


# ============================================================================
# Discrete Logarithm (Baby-Step Giant-Step)
# ============================================================================

@lru_cache(maxsize=128)
def discrete_log(h: int, g: int = PRIMITIVE_ROOT, p: int = PRIME_MODULUS) -> int:
    """
    Compute x such that g^x ≡ h (mod p) using baby-step giant-step algorithm.

    Complexity: O(√p) time, O(√p) space

    Args:
        h: Target value
        g: Base (primitive root)
        p: Prime modulus

    Returns:
        x where g^x ≡ h (mod p), or raises ValueError if no solution

    Algorithm (Shanks 1971):
        1. Choose m = ⌈√(p-1)⌉
        2. Baby steps: Compute g^j mod p for j = 0, 1, ..., m-1, store in table
        3. Compute c = g^(-m) mod p
        4. Giant steps: Compute γ = h × c^i for i = 0, 1, ..., m-1
        5. If γ is in table at position j, return x = i×m + j
    """
    if math.gcd(h, p) != 1:
        raise ValueError(f"discrete_log requires gcd(h={h}, p={p}) = 1")

    # Baby steps: build table of g^j mod p
    m = math.ceil(math.sqrt(p - 1))
    baby_table: Dict[int, int] = {}

    g_power = 1
    for j in range(m):
        if g_power not in baby_table:
            baby_table[g_power] = j
        g_power = (g_power * g) % p

    # Giant steps: search for collision
    c = pow(g, -m, p)  # g^(-m) mod p (using Fermat's little theorem)
    gamma = h

    for i in range(m):
        if gamma in baby_table:
            j = baby_table[gamma]
            x = (i * m + j) % (p - 1)
            # Verify solution
            assert pow(g, x, p) == h, f"discrete_log verification failed: {g}^{x} ≢ {h} (mod {p})"
            return x
        gamma = (gamma * c) % p

    raise ValueError(f"No solution found for {g}^x ≡ {h} (mod {p})")


# ============================================================================
# Legendre Symbol (for quadratic character)
# ============================================================================

def legendre_symbol(a: int, p: int) -> int:
    """
    Compute Legendre symbol (a/p) using Euler's criterion.

    (a/p) = a^((p-1)/2) mod p ∈ {-1, 0, 1}

    Returns:
        1  if a is quadratic residue mod p
        -1 if a is quadratic non-residue mod p
        0  if a ≡ 0 (mod p)
    """
    if a % p == 0:
        return 0

    result = pow(a, (p - 1) // 2, p)
    return -1 if result == p - 1 else result


# ============================================================================
# Character Implementations
# ============================================================================

def chi_71_a(n: int) -> complex:
    """
    χ₇₁.a - Principal character (trivial, identity).

    Order: 1 (χ^1 = χ₀)
    Bott[8] alignment: Class 0 (identity element)

    Definition: χ(n) = 1 for all gcd(n, 71) = 1

    Args:
        n: Integer argument

    Returns:
        1 if gcd(n, 71) = 1, else 0
    """
    return complex(1, 0) if math.gcd(n, PRIME_MODULUS) == 1 else complex(0, 0)


def chi_71_b(n: int) -> complex:
    """
    χ₇₁.b - Quadratic character (Legendre symbol).

    Order: 2 (χ^2 = χ₀)
    Bott[8] alignment: Class 1 (ℤ/2 symmetry)

    Definition: χ(n) = (n/71) (Legendre symbol)

    Args:
        n: Integer argument

    Returns:
        (n/71) ∈ {-1, 0, 1} as complex number
    """
    if math.gcd(n, PRIME_MODULUS) != 1:
        return complex(0, 0)

    leg = legendre_symbol(n, PRIME_MODULUS)
    return complex(leg, 0)


def chi_71_c(n: int) -> complex:
    """
    χ₇₁.c - Order 5 character (pentagonal symmetry).

    Order: 5
    Bott[8] alignment: Class 2

    Definition: χ(n) = ω^(k/14) where 7^k ≡ n (mod 71), ω = e^(2πi/5)

    Args:
        n: Integer argument

    Returns:
        5th root of unity raised to appropriate power
    """
    if math.gcd(n, PRIME_MODULUS) != 1:
        return complex(0, 0)

    k = discrete_log(n % PRIME_MODULUS)
    exponent = (k * 5) // 70  # k/14 reduced mod 5
    omega = complex(math.cos(2 * math.pi / 5), math.sin(2 * math.pi / 5))
    return omega ** exponent


def chi_71_d(n: int) -> complex:
    """
    χ₇₁.d - Order 7 character (heptagonal, Monster 7⁶ alignment).

    Order: 7
    Bott[8] alignment: Class 3

    Definition: χ(n) = ζ^(k/10) where 7^k ≡ n (mod 71), ζ = e^(2πi/7)

    Args:
        n: Integer argument

    Returns:
        7th root of unity raised to appropriate power
    """
    if math.gcd(n, PRIME_MODULUS) != 1:
        return complex(0, 0)

    k = discrete_log(n % PRIME_MODULUS)
    exponent = (k * 7) // 70  # k/10 reduced mod 7
    zeta = complex(math.cos(2 * math.pi / 7), math.sin(2 * math.pi / 7))
    return zeta ** exponent


def chi_71_e(n: int) -> complex:
    """
    χ₇₁.e - Order 10 character (quadratic-pentagonal product).

    Order: 10 = lcm(2, 5)
    Bott[8] alignment: Class 4

    Definition: χ(n) = χ₇₁.b(n) × χ₇₁.c(n)

    Args:
        n: Integer argument

    Returns:
        Product of quadratic and pentagonal characters
    """
    return chi_71_b(n) * chi_71_c(n)


def chi_71_f(n: int) -> complex:
    """
    χ₇₁.f - Order 14 character (quadratic-heptagonal product).

    Order: 14 = lcm(2, 7)
    Bott[8] alignment: Class 5

    Definition: χ(n) = χ₇₁.b(n) × χ₇₁.d(n)

    Args:
        n: Integer argument

    Returns:
        Product of quadratic and heptagonal characters
    """
    return chi_71_b(n) * chi_71_d(n)


def chi_71_g(n: int) -> complex:
    """
    χ₇₁.g - Order 35 character (pentagonal-heptagonal product).

    Order: 35 = lcm(5, 7)
    Bott[8] alignment: Class 6

    Definition: χ(n) = χ₇₁.c(n) × χ₇₁.d(n)

    Args:
        n: Integer argument

    Returns:
        Product of pentagonal and heptagonal characters
    """
    return chi_71_c(n) * chi_71_d(n)


def chi_71_h(n: int) -> complex:
    """
    χ₇₁.h - Order 70 character (maximal, full symmetry).

    Order: 70 = lcm(2, 5, 7) = φ(71) (maximal)
    Bott[8] alignment: Class 7 (singular, Gandalf role)

    Definition: χ(n) = χ₇₁.b(n) × χ₇₁.c(n) × χ₇₁.d(n)

    Args:
        n: Integer argument

    Returns:
        Product of all three primitive characters (maximal symmetry)
    """
    return chi_71_b(n) * chi_71_c(n) * chi_71_d(n)


# ============================================================================
# Character Registry
# ============================================================================

CHARACTERS = {
    'a': chi_71_a,
    'b': chi_71_b,
    'c': chi_71_c,
    'd': chi_71_d,
    'e': chi_71_e,
    'f': chi_71_f,
    'g': chi_71_g,
    'h': chi_71_h,
}


def get_character(label: str):
    """
    Get character function by label.

    Args:
        label: One of 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'

    Returns:
        Corresponding character function

    Raises:
        KeyError if label not in registry
    """
    if label not in CHARACTERS:
        raise KeyError(f"Unknown character label '{label}'. Valid: {list(CHARACTERS.keys())}")
    return CHARACTERS[label]


# ============================================================================
# Utility Functions
# ============================================================================

def character_table(max_n: int = 20) -> None:
    """
    Print character table for χ₇₁.{a-h} showing values at small integers.

    Useful for debugging and mathematical verification.

    Args:
        max_n: Maximum integer to display (default 20)
    """
    print(f"{'n':>4}", end="")
    for label in CHARACTERS:
        print(f"  χ₇₁.{label:1s}", end="")
    print()
    print("-" * (6 + 8 * len(CHARACTERS)))

    for n in range(1, min(max_n + 1, PRIME_MODULUS)):
        if math.gcd(n, PRIME_MODULUS) != 1:
            continue
        print(f"{n:4d}", end="")
        for label, chi in CHARACTERS.items():
            val = chi(n)
            # Format complex number compactly
            if abs(val.imag) < 1e-10:
                print(f"  {val.real:5.2f}", end="")
            else:
                print(f"  {val.real:+.1f}{val.imag:+.1f}i", end="")
        print()


if __name__ == "__main__":
    print("=" * 70)
    print("Dirichlet Characters Modulo 71 - χ₇₁.{a-h}")
    print("=" * 70)
    print()

    # Verify primitive root
    print(f"Primitive root verification: g={PRIMITIVE_ROOT} mod {PRIME_MODULUS}")
    is_primitive = verify_primitive_root(PRIMITIVE_ROOT, PRIME_MODULUS)
    print(f"  Result: {'✓ VERIFIED' if is_primitive else '✗ FAILED'}")
    print()

    # Display character orders
    print("Character orders:")
    for label, order in CHARACTER_ORDERS.items():
        print(f"  χ₇₁.{label}: order {order:2d} (Bott[{ord(label) - ord('a')}])")
    print()

    # Show character table
    print("Character values for small n:")
    character_table(max_n=15)
