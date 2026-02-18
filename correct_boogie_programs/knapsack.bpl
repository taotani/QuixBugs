function max(a: int, b: int) : int { if a > b then a else b }

procedure knapsack(capacity: int, weights: [int]int, values: [int]int, n: int) returns (result: int)
    requires capacity >= 0 && n >= 0;
    requires (forall k: int :: 0 <= k && k < n ==> weights[k] >= 0);
{
    var memo: [int, int]int;
    var i, j, weight, value: int;

    i := 0;
    while (i <= n)
        invariant 0 <= i && i <= n + 1;
    {
        if (i > 0) {
            weight := weights[i-1];
            value := values[i-1];
        }
        j := 0;
        while (j <= capacity)
            invariant 0 <= j && j <= capacity + 1;
        {
            if (i == 0 || j == 0) {
                memo[i, j] := 0;
            } else if (weight <= j) {
                memo[i, j] := max(memo[i-1, j], value + memo[i-1, j - weight]);
            } else {
                memo[i, j] := memo[i-1, j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
    result := memo[n, capacity];
}
