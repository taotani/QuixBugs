procedure sieve(max: int) returns (primes: [int]int, n_primes: int)
    requires max >= 2;
{
    var n, i: int;
    var all_not_divisible: bool;

    n_primes := 0;
    n := 2;
    while (n <= max)
        invariant 2 <= n && n <= max + 1;
    {
        all_not_divisible := true;
        i := 0;
        while (i < n_primes)
            invariant 0 <= i && i <= n_primes;
        {
            if (n mod primes[i] == 0)
            {
                all_not_divisible := false;
            }
            i := i + 1;
        }

        if (all_not_divisible)
        {
            primes[n_primes] := n;
            n_primes := n_primes + 1;
        }
        n := n + 1;
    }
}
