function PrefixDepth(parens: [int]int, k: int) : int;
axiom (forall parens: [int]int :: PrefixDepth(parens, 0) == 0);
axiom (forall parens: [int]int, k: int :: k >= 0 ==> PrefixDepth(parens, k + 1) == PrefixDepth(parens, k) + (if parens[k] == 40 then 1 else -1));

procedure is_valid_parenthesization(parens: [int]int, n: int) returns (result: bool)
    requires n >= 0;
    // Buggy specification: only checks that depth never drops below zero
    ensures result <==> (forall k: int :: 0 <= k && k <= n ==> PrefixDepth(parens, k) >= 0);
{
    var depth: int;
    var i: int;
    depth := 0;
    i := 0;
    while (i < n)
        invariant 0 <= i && i <= n;
        invariant depth == PrefixDepth(parens, i);
        invariant (forall k: int :: 0 <= k && k <= i ==> PrefixDepth(parens, k) >= 0);
    {
        if (parens[i] == 40) {
            depth := depth + 1;
        } else {
            depth := depth - 1;
            if (depth < 0) {
                result := false;
                return;
            }
        }
        i := i + 1;
    }
    result := true;
}
