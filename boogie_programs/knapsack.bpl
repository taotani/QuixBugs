function max(a: int, b: int) : int { if a > b then a else b }

function BuggyKnapsack(capacity: int, weights: [int]int, values: [int]int, n: int) : int;
axiom (forall c: int, w: [int]int, v: [int]int, n: int :: 
    BuggyKnapsack(c, w, v, n) == 
    (if n == 0 || c <= 0 then 0 else
        (if w[n-1] < c then max(BuggyKnapsack(c, w, v, n-1), v[n-1] + BuggyKnapsack(c - w[n-1], w, v, n-1))
        else BuggyKnapsack(c, w, v, n-1))));

procedure knapsack(capacity: int, weights: [int]int, values: [int]int, n: int) returns (result: int)
    requires capacity >= 0 && n >= 0;
    requires (forall k: int :: 0 <= k && k < n ==> weights[k] >= 0);
    ensures result == BuggyKnapsack(capacity, weights, values, n);
{
    var memo: [int, int]int;
    var i, j, weight, value: int;

    i := 0;
    while (i <= n)
        invariant 0 <= i && i <= n + 1;
        invariant (forall k: int :: 0 <= k && k <= capacity ==> memo[i, k] == BuggyKnapsack(k, weights, values, i));
    {
        if (i > 0) {
            weight := weights[i-1];
            value := values[i-1];
        }
        j := 0;
        while (j <= capacity)
            invariant 0 <= j && j <= capacity + 1;
            invariant (forall k: int :: 0 <= k && k < j ==> memo[i, k] == BuggyKnapsack(k, weights, values, i));
        {
            if (i == 0 || j == 0) {
                memo[i, j] := 0;
            } else if (weight < j) {
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
