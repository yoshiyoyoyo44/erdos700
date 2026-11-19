"""Reproduce the numerical checks for fixed cofactors and the small prime-power families."""
from verify_erdos700_general import brute, cofactor_value, factor, large_prime_equal


def is_power_of_two(value):
    return value > 0 and value & (value - 1) == 0


def has_max_digit(value, base):
    while value:
        value, digit = divmod(value, base)
        if digit == base - 1:
            return True
    return False


def block_bases(m):
    bases = []
    for prime, exponent in factor(m).items():
        ceiling_power = prime
        while ceiling_power < m:
            ceiling_power *= prime
        bases.append(ceiling_power * prime ** (exponent - 1))
    return bases


def run_checks():
    primes = [p for p in range(2, 100_001) if factor(p) == {p: 1}]
    large_primes = [p for p in primes if p > 8]
    exceptions = []
    direct_checks = 0
    for p in large_primes:
        exceptional = is_power_of_two(p - 1) or is_power_of_two(3 * p - 1)
        predicted = 4 if exceptional else 8
        assert cofactor_value(8, p, 1) == predicted, p
        if p <= 500:
            assert brute(8 * p) == predicted, p
            direct_checks += 1
        if exceptional:
            exceptions.append(p)
    print(f"8p: {len(large_primes)} primes, {direct_checks} direct row checks")
    print(f"Exceptions: {exceptions}")

    checked_pairs = 0
    block_hits = 0
    for m in range(2, 37):
        bases = block_bases(m)
        for p in primes:
            if p > 1000:
                break
            if p <= m:
                continue
            equality = cofactor_value(m, p, 1) == m
            assert large_prime_equal(m, p) == equality, (m, p)
            if all(has_max_digit(p, base) for base in bases):
                assert equality, (m, p, bases)
                block_hits += 1
            checked_pairs += 1
    print(f"Fixed cofactors: {checked_pairs} (m, p) pairs, {block_hits} block certificates")

    power_checks = 0
    direct_power_checks = 0
    for q in primes:
        if q > 2000:
            break
        if q == 2:
            continue
        for e in range(1, 65):
            expected = 3 if (q, e) == (3, 1) else 4
            assert cofactor_value(4, q, e) == expected, (q, e)
            if 4 * q**e <= 2500:
                assert brute(4 * q**e) == expected, (q, e)
                direct_power_checks += 1
            power_checks += 1
    for e in range(1, 513):
        assert cofactor_value(6, 5, e) == 6, e
        if 6 * 5**e <= 2500:
            assert brute(6 * 5**e) == 6, e
            direct_power_checks += 1
        power_checks += 1
    print(f"Small cofactors: {power_checks} prime powers, {direct_power_checks} direct row checks")


if __name__ == "__main__":
    run_checks()
