function max(a: int, b: int) : int { if a > b then a else b }

procedure lis(arr: [int]int, n: int) returns (longest: int)
{
    var ends: [int]int;
    var i, j, val, length: int;

    longest := 0;
    i := 0;
    while (i < n)
        invariant 0 <= i && i <= n;
    {
        val := arr[i];
        length := 0;
        j := 1;
        while (j <= longest)
            invariant 1 <= j && j <= longest + 1;
        {
            if (arr[ends[j]] < val)
            {
                length := j;
            }
            j := j + 1;
        }

        if (length == longest || val < arr[ends[length + 1]])
        {
            ends[length + 1] := i;
            longest := max(longest, length + 1);
        }
        i := i + 1;
    }
}
