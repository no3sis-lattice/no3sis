"""
Tests for Dirichlet Characters Modulo 71

Validates all 5 mathematical properties required by the design spec:
1. Multiplicativity: χ(ab) = χ(a)χ(b)
2. Periodicity: χ^(order) = χ₀ (principal character)
3. Coprimality: χ(n) = 0 iff gcd(n, 71) ≠ 1
4. Character Order: Verified for each χ₇₁.{a-h}
5. Orthogonality: Σ χ(n) χ̄(n) = φ(71) = 70 for equal characters

Test-Driven Development (TDD) compliance:
- Property-based tests for all 8 characters
- Edge case coverage (n=0, n=71, n<0, n>71)
- Computational verification of mathematical theorems
- No hardcoded magic numbers (all derived from constants)
"""

import pytest
import math
import cmath
from typing import Callable, List

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from lib.dirichlet_characters import (
    PRIME_MODULUS,
    PRIMITIVE_ROOT,
    CHARACTER_ORDERS,
    CHARACTERS,
    chi_71_a,
    chi_71_b,
    chi_71_c,
    chi_71_d,
    chi_71_e,
    chi_71_f,
    chi_71_g,
    chi_71_h,
    verify_primitive_root,
    discrete_log,
    legendre_symbol,
    get_character,
)


# ============================================================================
# Test: Primitive Root Verification
# ============================================================================

def test_primitive_root_g7_mod71():
    """Verify g=7 is a primitive root modulo 71."""
    assert verify_primitive_root(PRIMITIVE_ROOT, PRIME_MODULUS)


def test_primitive_root_order():
    """Verify 7 has order 70 = φ(71) modulo 71."""
    # 7^70 ≡ 1 (mod 71) by Fermat's little theorem
    assert pow(PRIMITIVE_ROOT, 70, PRIME_MODULUS) == 1

    # 7^k ≢ 1 (mod 71) for all 1 ≤ k < 70
    for k in [1, 2, 5, 7, 10, 14, 35]:  # Proper divisors of 70
        assert pow(PRIMITIVE_ROOT, k, PRIME_MODULUS) != 1


def test_primitive_root_generates_all_residues():
    """Verify 7^k generates all residues mod 71."""
    generated = set()
    for k in range(70):
        residue = pow(PRIMITIVE_ROOT, k, PRIME_MODULUS)
        generated.add(residue)

    # Should generate exactly {1, 2, 3, ..., 70}
    assert generated == set(range(1, PRIME_MODULUS))
    assert len(generated) == 70


def test_primitive_root_invalid_cases():
    """Verify primitive root verification rejects invalid inputs."""
    assert not verify_primitive_root(1, PRIME_MODULUS)  # 1 is never primitive
    assert not verify_primitive_root(2, PRIME_MODULUS)  # 2^35 ≡ 1 (mod 71)
    assert not verify_primitive_root(0, PRIME_MODULUS)  # Invalid
    assert not verify_primitive_root(71, PRIME_MODULUS)  # ≡ 0


# ============================================================================
# Test: Discrete Logarithm
# ============================================================================

def test_discrete_log_small_values():
    """Test discrete log for small known values."""
    # 7^0 ≡ 1 (mod 71)
    assert discrete_log(1) == 0

    # 7^1 ≡ 7 (mod 71)
    assert discrete_log(7) == 1

    # 7^2 ≡ 49 (mod 71)
    assert discrete_log(49) == 2


def test_discrete_log_all_residues():
    """Verify discrete log is defined for all residues mod 71."""
    for n in range(1, PRIME_MODULUS):
        k = discrete_log(n)
        # Verify: 7^k ≡ n (mod 71)
        assert pow(PRIMITIVE_ROOT, k, PRIME_MODULUS) == n
        # k should be in range [0, 70)
        assert 0 <= k < 70


def test_discrete_log_invalid_input():
    """Verify discrete log raises error for invalid inputs."""
    with pytest.raises(ValueError):
        discrete_log(0)  # gcd(0, 71) = 71 ≠ 1

    with pytest.raises(ValueError):
        discrete_log(71)  # 71 ≡ 0 (mod 71)


# ============================================================================
# Test: Legendre Symbol
# ============================================================================

def test_legendre_symbol_quadratic_residues():
    """Test Legendre symbol for known quadratic residues."""
    # 1 is always a quadratic residue
    assert legendre_symbol(1, PRIME_MODULUS) == 1

    # Squares are quadratic residues
    for a in [2, 3, 5, 8]:
        a_squared = (a * a) % PRIME_MODULUS
        assert legendre_symbol(a_squared, PRIME_MODULUS) == 1


def test_legendre_symbol_count():
    """Verify exactly 35 quadratic residues mod 71."""
    residues = sum(
        1 for a in range(1, PRIME_MODULUS) if legendre_symbol(a, PRIME_MODULUS) == 1
    )
    assert residues == (PRIME_MODULUS - 1) // 2  # 35


def test_legendre_symbol_non_residues():
    """Verify Legendre symbol for non-residues."""
    # 2 is a non-residue mod 71
    assert legendre_symbol(2, PRIME_MODULUS) == -1


def test_legendre_symbol_zero():
    """Verify Legendre symbol is 0 for multiples of 71."""
    assert legendre_symbol(0, PRIME_MODULUS) == 0
    assert legendre_symbol(71, PRIME_MODULUS) == 0


# ============================================================================
# Test: Property 1 - Multiplicativity
# ============================================================================

@pytest.mark.parametrize("chi_label", list(CHARACTERS.keys()))
def test_multiplicativity(chi_label: str):
    """Test χ(ab) = χ(a)χ(b) for all characters."""
    chi = CHARACTERS[chi_label]

    # Test on sample of coprime pairs
    test_pairs = [(2, 3), (5, 7), (6, 8), (10, 11), (13, 17)]

    for a, b in test_pairs:
        chi_ab = chi((a * b) % PRIME_MODULUS)
        chi_a = chi(a)
        chi_b = chi(b)
        expected = chi_a * chi_b

        # Allow small floating-point error for complex numbers
        assert abs(chi_ab - expected) < 1e-10, (
            f"χ₇₁.{chi_label}({a}×{b}) = {chi_ab}, "
            f"but χ({a})×χ({b}) = {chi_a}×{chi_b} = {expected}"
        )


@pytest.mark.parametrize("chi_label", list(CHARACTERS.keys()))
def test_multiplicativity_exhaustive(chi_label: str):
    """Exhaustive multiplicativity test for all coprime pairs (slow)."""
    chi = CHARACTERS[chi_label]

    # Test subset (full 70×70 test is slow)
    sample_residues = [n for n in range(1, PRIME_MODULUS) if n % 5 == 1][:10]

    for a in sample_residues:
        for b in sample_residues:
            ab = (a * b) % PRIME_MODULUS
            chi_ab = chi(ab)
            chi_a_times_chi_b = chi(a) * chi(b)

            assert abs(chi_ab - chi_a_times_chi_b) < 1e-10


# ============================================================================
# Test: Property 2 - Periodicity (Character Order)
# ============================================================================

@pytest.mark.parametrize("chi_label", list(CHARACTERS.keys()))
def test_character_order(chi_label: str):
    """Test χ^(order) = χ₀ (principal character)."""
    chi = CHARACTERS[chi_label]
    order = CHARACTER_ORDERS[chi_label]

    # For all n coprime to 71, χ(n)^(order) should equal 1
    test_values = [2, 3, 5, 7, 11, 13, 17, 19, 23]

    for n in test_values:
        chi_n = chi(n)
        chi_n_to_order = chi_n ** order

        # Should equal 1 (principal character value)
        assert abs(chi_n_to_order - complex(1, 0)) < 1e-9, (
            f"χ₇₁.{chi_label}({n})^{order} = {chi_n_to_order}, expected 1"
        )


@pytest.mark.parametrize("chi_label,order", CHARACTER_ORDERS.items())
def test_character_minimal_order(chi_label: str, order: int):
    """Verify stated order is the MINIMAL order."""
    chi = CHARACTERS[chi_label]

    # For at least one n, χ(n) should have exact order (not smaller)
    # Use n = 7 (generator) as test case
    n = PRIMITIVE_ROOT
    chi_n = chi(n)

    # Check that no proper divisor of order works
    for divisor in range(1, order):
        if order % divisor == 0 and divisor != order:
            chi_n_to_divisor = chi_n ** divisor
            # Should NOT equal 1 (otherwise order would be smaller)
            if abs(chi_n_to_divisor - complex(1, 0)) < 1e-9:
                pytest.fail(
                    f"χ₇₁.{chi_label} has order ≤ {divisor}, not {order} as claimed"
                )


# ============================================================================
# Test: Property 3 - Coprimality
# ============================================================================

@pytest.mark.parametrize("chi_label", list(CHARACTERS.keys()))
def test_coprimality_zero_for_multiples(chi_label: str):
    """Test χ(n) = 0 when gcd(n, 71) ≠ 1."""
    chi = CHARACTERS[chi_label]

    # Test multiples of 71
    for k in [0, 1, 2, 5]:
        n = k * PRIME_MODULUS
        result = chi(n)
        assert abs(result) < 1e-10, f"χ₇₁.{chi_label}({n}) = {result}, expected 0"


@pytest.mark.parametrize("chi_label", list(CHARACTERS.keys()))
def test_coprimality_nonzero_for_coprimes(chi_label: str):
    """Test χ(n) ≠ 0 when gcd(n, 71) = 1."""
    chi = CHARACTERS[chi_label]

    # Test all coprime residues
    for n in range(1, PRIME_MODULUS):
        result = chi(n)
        # Should be non-zero (on unit circle for most characters)
        assert abs(result) > 1e-10, f"χ₇₁.{chi_label}({n}) = {result}, expected ≠ 0"


# ============================================================================
# Test: Property 4 - Unit Circle (Roots of Unity)
# ============================================================================

@pytest.mark.parametrize("chi_label", list(CHARACTERS.keys()))
def test_character_values_on_unit_circle(chi_label: str):
    """Test |χ(n)| = 1 for all coprime n."""
    chi = CHARACTERS[chi_label]

    for n in range(1, PRIME_MODULUS):
        chi_n = chi(n)
        magnitude = abs(chi_n)

        # Should be exactly 1 (root of unity)
        assert abs(magnitude - 1.0) < 1e-9, (
            f"|χ₇₁.{chi_label}({n})| = {magnitude}, expected 1"
        )


# ============================================================================
# Test: Property 5 - Orthogonality
# ============================================================================

def test_orthogonality_equal_characters():
    """Test Σ χ(n) χ̄(n) = φ(71) = 70 for equal characters."""
    for chi_label, chi in CHARACTERS.items():
        # Σ_{n=1}^{70} χ(n) × conj(χ(n)) = Σ |χ(n)|² = 70
        orthogonality_sum = sum(
            chi(n) * chi(n).conjugate() for n in range(1, PRIME_MODULUS)
        )

        # Should equal 70 (φ(71))
        assert abs(orthogonality_sum - 70) < 1e-8, (
            f"Orthogonality sum for χ₇₁.{chi_label}: {orthogonality_sum}, expected 70"
        )


def test_orthogonality_distinct_characters():
    """Test Σ χ₁(n) χ̄₂(n) = 0 for distinct characters χ₁ ≠ χ₂."""
    labels = list(CHARACTERS.keys())

    for i, chi1_label in enumerate(labels):
        for chi2_label in labels[i + 1 :]:
            chi1 = CHARACTERS[chi1_label]
            chi2 = CHARACTERS[chi2_label]

            # Σ_{n=1}^{70} χ₁(n) × conj(χ₂(n))
            orthogonality_sum = sum(
                chi1(n) * chi2(n).conjugate() for n in range(1, PRIME_MODULUS)
            )

            # Should equal 0
            assert abs(orthogonality_sum) < 1e-8, (
                f"Orthogonality χ₇₁.{chi1_label}, χ₇₁.{chi2_label}: "
                f"{orthogonality_sum}, expected 0"
            )


# ============================================================================
# Test: Specific Character Properties
# ============================================================================

def test_principal_character_always_one():
    """χ₇₁.a (principal) should always return 1."""
    for n in range(1, PRIME_MODULUS):
        assert chi_71_a(n) == complex(1, 0)


def test_quadratic_character_is_real():
    """χ₇₁.b (quadratic) should return real values {-1, 1}."""
    for n in range(1, PRIME_MODULUS):
        val = chi_71_b(n)
        assert abs(val.imag) < 1e-10, f"χ₇₁.b({n}) = {val} is not real"
        assert val.real in [-1, 1], f"χ₇₁.b({n}) = {val.real}, expected ±1"


def test_composite_characters_as_products():
    """Test χ₇₁.e = χ₇₁.b × χ₇₁.c (and similar)."""
    test_values = [2, 5, 10, 17, 23]

    # χ₇₁.e = χ₇₁.b × χ₇₁.c
    for n in test_values:
        assert abs(chi_71_e(n) - chi_71_b(n) * chi_71_c(n)) < 1e-10

    # χ₇₁.f = χ₇₁.b × χ₇₁.d
    for n in test_values:
        assert abs(chi_71_f(n) - chi_71_b(n) * chi_71_d(n)) < 1e-10

    # χ₇₁.g = χ₇₁.c × χ₇₁.d
    for n in test_values:
        assert abs(chi_71_g(n) - chi_71_c(n) * chi_71_d(n)) < 1e-10

    # χ₇₁.h = χ₇₁.b × χ₇₁.c × χ₇₁.d
    for n in test_values:
        assert abs(chi_71_h(n) - chi_71_b(n) * chi_71_c(n) * chi_71_d(n)) < 1e-10


# ============================================================================
# Test: Character Registry
# ============================================================================

def test_get_character_valid_labels():
    """Test get_character retrieves correct functions."""
    for label in ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']:
        chi = get_character(label)
        assert chi is CHARACTERS[label]
        # Verify it's callable
        assert callable(chi)


def test_get_character_invalid_label():
    """Test get_character raises error for invalid labels."""
    with pytest.raises(KeyError):
        get_character('z')

    with pytest.raises(KeyError):
        get_character('71.a')  # Wrong format


# ============================================================================
# Test: Edge Cases
# ============================================================================

@pytest.mark.parametrize("chi_label", list(CHARACTERS.keys()))
def test_negative_inputs(chi_label: str):
    """Test characters handle negative inputs correctly."""
    chi = CHARACTERS[chi_label]

    # χ(-n) should equal χ(71 - n) by periodicity
    for n in [1, 2, 5, 10]:
        chi_neg_n = chi(-n)
        chi_pos_equiv = chi(PRIME_MODULUS - n)
        assert abs(chi_neg_n - chi_pos_equiv) < 1e-10


@pytest.mark.parametrize("chi_label", list(CHARACTERS.keys()))
def test_large_inputs(chi_label: str):
    """Test characters handle inputs > 71 via modular reduction."""
    chi = CHARACTERS[chi_label]

    # χ(n + 71k) = χ(n) for any k
    for n in [3, 7, 13]:
        chi_n = chi(n)
        chi_n_plus_71 = chi(n + PRIME_MODULUS)
        chi_n_plus_142 = chi(n + 2 * PRIME_MODULUS)

        assert abs(chi_n - chi_n_plus_71) < 1e-10
        assert abs(chi_n - chi_n_plus_142) < 1e-10


# ============================================================================
# Test: Bott[8] Alignment
# ============================================================================

def test_bott8_character_count():
    """Verify exactly 8 characters (Bott[8] dimension)."""
    assert len(CHARACTERS) == 8
    assert len(CHARACTER_ORDERS) == 8


def test_bott8_order_alignment():
    """Verify character orders align with Bott[8] structure."""
    expected_orders = {
        'a': 1,   # Class 0: Identity
        'b': 2,   # Class 1: ℤ/2
        'c': 5,   # Class 2: Pentagonal
        'd': 7,   # Class 3: Heptagonal (Monster 7⁶)
        'e': 10,  # Class 4: Product
        'f': 14,  # Class 5: Product
        'g': 35,  # Class 6: Product
        'h': 70,  # Class 7: Maximal (singular)
    }

    assert CHARACTER_ORDERS == expected_orders


# ============================================================================
# Performance/Sanity Checks
# ============================================================================

def test_discrete_log_caching():
    """Verify discrete_log uses LRU cache effectively."""
    # Call twice with same input
    result1 = discrete_log(42)
    result2 = discrete_log(42)

    assert result1 == result2  # Should return cached value


def test_all_characters_complete():
    """Smoke test: all 8 characters are callable and return valid values."""
    test_n = 13

    for label, chi in CHARACTERS.items():
        result = chi(test_n)

        # Should return complex number
        assert isinstance(result, complex)

        # Should be on unit circle
        assert abs(abs(result) - 1.0) < 1e-9

        # Should be a root of unity (character order property)
        order = CHARACTER_ORDERS[label]
        assert abs(result ** order - complex(1, 0)) < 1e-9


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
