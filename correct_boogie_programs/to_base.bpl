procedure to_base(num_in: int, b: int) returns (result: [int]int, n: int)
    requires num_in > 0 && b > 1;
{
    var num, i, k: int;
    num := num_in;
    n := 0;
    while (num > 0)
        invariant num >= 0;
    {
        i := num mod b;
        num := num div b;

        k := n;
        while (k > 0)
            invariant 0 <= k && k <= n;
        {
            result[k] := result[k - 1];
            k := k - 1;
        }
        result[0] := i;
        n := n + 1;
    }
}
