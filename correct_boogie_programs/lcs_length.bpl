function max(a: int, b: int) : int { if a > b then a else b }

procedure lcs_length(s: [int]int, n_s: int, t: [int]int, n_t: int) returns (result: int)
{
    var dp: [int, int]int;
    var i, j: int;

    result := 0;
    i := 0;
    while (i < n_s)
        invariant 0 <= i && i <= n_s;
    {
        j := 0;
        while (j < n_t)
            invariant 0 <= j && j <= n_t;
        {
            if (s[i] == t[j])
            {
                dp[i, j] := (if i > 0 && j > 0 then dp[i - 1, j - 1] else 0) + 1;
            }
            else
            {
                dp[i, j] := 0;
            }
            result := max(result, dp[i, j]);
            j := j + 1;
        }
        i := i + 1;
    }
}
