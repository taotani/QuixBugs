procedure to_base(num_in: int, b: int) returns (result: [int]int, n: int)
    requires num_in > 0 && b > 1;
{
    var num, i: int;
    num := num_in;
    n := 0;
    while (num > 0)
        invariant num >= 0;
    {
        i := num mod b;
        num := num div b;
        result[n] := i;
        n := n + 1;
    }
}
