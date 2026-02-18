procedure next_permutation(perm: [int]int, n: int) returns (next_perm: [int]int)
{
    var i, j, k, q, temp: int;
    next_perm := perm;
    i := n - 2;
    while (i >= 0)
        invariant -1 <= i && i <= n - 2;
    {
        if (perm[i] < perm[i + 1])
        {
            j := n - 1;
            while (j > i)
                invariant i <= j && j <= n - 1;
            {
                if (perm[j] < perm[i])
                {
                    temp := next_perm[i];
                    next_perm[i] := next_perm[j];
                    next_perm[j] := temp;

                    // Reverse from i + 1 to n - 1
                    k := 0;
                    while (i + 1 + k < n - 1 - k)
                    {
                        temp := next_perm[i + 1 + k];
                        next_perm[i + 1 + k] := next_perm[n - 1 - k];
                        next_perm[n - 1 - k] := temp;
                        k := k + 1;
                    }
                    return;
                }
                j := j - 1;
            }
        }
        i := i - 1;
    }
}
