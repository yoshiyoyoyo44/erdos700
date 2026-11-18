"""Check equality in Erdos-Szekeres problem 700(a) (Python standard library)."""
from itertools import product
from math import comb, gcd, lcm


def factor(n):
    factors = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        factors[n] = 1
    return factors


def critical_divisors(factors):
    """Divisibility-minimal divisors above the greatest prime-power factor."""
    ceiling = max(p**a for p, a in factors.items())
    primes = tuple(factors)
    for exponents in product(*(range(factors[p]+1) for p in primes)):
        active = [(p, b) for p, b in zip(primes, exponents) if b]
        if not active:
            continue
        d = 1
        for p, b in active:
            d *= p**b
        if d > ceiling and d//min(p for p, b in active) <= ceiling:
            yield d, active


def powers_mask(place, lo, hi):
    """Bits at lo*place, ..., hi*place. Successive positions differ by place."""
    if lo > hi:
        return 0
    repeats = ((1 << ((hi-lo+1)*place)) - 1) // ((1 << place) - 1)
    return repeats << (lo*place)


def digit_mask(n, p, budget):
    """Borrow-count masks, by reading the digits of n. No binomial coefficients."""
    states = {(0, 0): 1}  # (borrows used, incoming borrow), starting with k=0
    place, remaining = 1, n
    while remaining:
        remaining, digit = divmod(remaining, p)
        updated = {}
        for (used, incoming), partial in states.items():
            cutoff = digit-incoming
            no_borrow = powers_mask(place, 0, cutoff)
            if no_borrow:
                state = (used, 0)
                updated[state] = updated.get(state, 0) + partial*no_borrow
            if remaining and used < budget:
                borrow = powers_mask(place, cutoff+1, p-1)
                if borrow:
                    state = (used+1, 1)
                    updated[state] = updated.get(state, 0) + partial*borrow
        states = updated
        place *= p
    return sum(states.values())


def criterion(n):
    """Return the two equality answers (largest power, largest prime) and a witness."""
    factors = factor(n)
    if len(factors) == 1:
        p, exponent = next(iter(factors.items()))
        if exponent < 2:
            raise ValueError("expected a composite integer")
        return False, exponent == 2, None
    if not factors:
        raise ValueError("expected a composite integer")
    ceiling = max(p**a for p, a in factors.items())
    endpoints = (1 << n) + 1
    masks = {}
    for d, active in critical_divisors(factors):
        overlap = None
        for p, b in active:
            key = p, factors[p]-b
            if key not in masks:
                masks[key] = digit_mask(n, *key)
            overlap = masks[key] if overlap is None else overlap & masks[key]
            if overlap == endpoints:
                break
        if overlap != endpoints:
            interior = overlap ^ endpoints
            k = (interior & -interior).bit_length()-1
            assert 2 <= k <= n//2 and k % d == 0
            return False, False, (d, k)
    return True, ceiling == max(factors), None


def digit_sum(n, p):
    if p == 2:
        return n.bit_count()
    total = 0
    while n:
        n, digit = divmod(n, p)
        total += digit
    return total


def carry_count(x, y, p):
    return (digit_sum(x,p) + digit_sum(y,p) - digit_sum(x+y,p)) // (p-1)


def cofactor_value(m, q, e):
    """Exact f(m*q**e) for m>=2, prime q not dividing m."""
    if m < 2 or e < 1 or gcd(m, q) != 1:
        raise ValueError("expected m>=2, e>=1 and q coprime to m")
    factors = factor(m)
    B = 1
    h = 0
    while h < e and B*q < m:
        B *= q
        h += 1
    z, A = q**(e-h), m*B
    smallest = m                          # achieved at k=q**e
    for t in range(1, A//2+1):
        qpart = q**min(e, carry_count(t, A-t, q))
        if qpart*(m//gcd(m,t)) >= smallest:
            continue
        g = qpart
        for p, a in factors.items():
            g *= p**min(a, carry_count(t*z, (A-t)*z, p))
        smallest = min(smallest, g)
    return smallest


def brute(n):
    """Exact integer recurrence; all admissible columns included."""
    value, coefficient = n, n
    for k in range(2, n//2+1):
        coefficient = coefficient*(n-k+1)//k
        value = min(value, gcd(n, coefficient))
    return value


def valuation(x, p):
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def partition_mask(n, p, budget):
    """Construct the refinement/subsum set literally for small audit inputs."""
    digits, u = [], n
    while u:
        u, digit = divmod(u, p)
        digits.append(digit)
    levels = {tuple(digits)}
    seen, result = set(), 0
    for step in range(budget+1):
        following = set()
        for counts in levels:
            if counts in seen:
                continue
            seen.add(counts)
            bits = 1
            for j, count in enumerate(counts):
                weight = p**j
                for _ in range(count):
                    bits |= bits << weight
                if step < budget and j and count:
                    new = list(counts)
                    new[j] -= 1
                    new[j-1] += p
                    following.add(tuple(new))
            result |= bits
        levels = following
    return result


def ternary_has_two(x):
    while x:
        x, digit = divmod(x, 3)
        if digit == 2:
            return True
    return False


def digit_pair_reaches(m, t, x, base, target):
    """Read x in base 'base' and count carries in t*x + (m-t)*x."""
    left = right = incoming = count = 0
    while x or left or right or incoming:
        x, digit = divmod(x, base)
        left, d_left = divmod(t*digit + left, base)
        right, d_right = divmod((m-t)*digit + right, base)
        incoming = (d_left + d_right + incoming) // base
        count += incoming
        if count >= target:
            return True
    return False


def large_prime_equal(m, prime):
    """Finite-state test for f(m*prime)=m with prime>m>=2."""
    assert prime > m >= 2
    return all(digit_pair_reaches(m, t, prime, p, a)
               for p, a in factor(m).items() for t in range(1, m//2+1))


def equality_progression_step(m, q, seed):
    """A period that preserves equality from a successful seed with q**(seed+1)>=m."""
    assert q**(seed+1) >= m and cofactor_value(m, q, seed) == m
    n = m*q**seed
    period = 1
    for p in factor(m):
        modulus = p
        while modulus <= n:
            modulus *= p
        order = modulus//p * (p-1)
        for r in set(factor(p-1)) | {p}:
            while order % r == 0 and pow(q, order//r, modulus) == 1:
                order //= r
        period = lcm(period, order)
    return period


def run_checks(limit=5000):
    composites, power_yes, prime_yes = 0, 0, 0
    for n in range(4, limit+1):
        factors = factor(n)
        if sum(factors.values()) < 2:
            continue
        f = brute(n)
        Q = max(p**a for p, a in factors.items())
        a, b, witness = criterion(n)
        assert a == (f == n//Q) and b == (f == n//max(factors)), (n, a, b, f)
        if witness:
            d, k = witness
            assert (n//d) % gcd(n, comb(n,k)) == 0
        if len(factors) > 1:
            p = max(factors, key=lambda p: p**factors[p])
            assert cofactor_value(n//Q, p, factors[p]) == f, (n,f)
            if factors[p] == 1 and p > n//p:
                assert large_prime_equal(n//p, p) == (f == n//p), n
        if n <= 144:
            for p, e in factors.items():
                for budget in range(e):
                    bits = sum(1 << k for k in range(n+1)
                               if valuation(comb(n,k),p) <= budget)
                    assert digit_mask(n,p,budget) == bits, (n,p,budget)
                    assert partition_mask(n,p,budget) == bits, (n,p,budget)
        composites += 1
        power_yes += a
        prime_yes += b
    print(f"n <= {limit}: {composites} composites, {power_yes} power equalities, {prime_yes} prime equalities",flush=True)
    for n in (12,30,45,210,1694,4608,10815):
        print(n, brute(n), criterion(n))
    for e in range(4,1025):
        assert cofactor_value(9,2,e) == (9 if ternary_has_two(2**(e-1)) else 4), e
    print("fixed power identity checked for e=4..1024")
    assert [carry_count(t,72-t,2) for t in (9,18,27,36)] == [6,4,6,2]
    assert [carry_count(t,18-t,2) for t in (3,6)] == [4,2]
    for m, q, seed in ((6,5,1), (9,2,4), (4,3,2)):
        step = equality_progression_step(m, q, seed)
        assert all(cofactor_value(m, q, seed+j*step) == m for j in range(4))
        print("equality progression", m, q, seed, step)
    for p in range(71, 5000, 72):
        if factor(p) == {p: 1}:
            assert large_prime_equal(6, p)


if __name__ == "__main__":
    run_checks()
