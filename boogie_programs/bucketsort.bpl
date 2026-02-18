procedure bucketsort(arr: [int]int, n: int, k: int) returns (sorted_arr: [int]int)
    requires n >= 0 && k > 0;
    requires (forall i: int :: 0 <= i && i < n ==> 0 <= arr[i] && arr[i] < k);
    // Buggy specification: does not enforce sorting, only safe execution
{
    var counts: [int]int;
    var i, x, count, j, p: int;

    counts := (lambda m: int :: 0);
    i := 0;
    while (i < n)
        invariant 0 <= i && i <= n;
    {
        x := arr[i];
        counts[x] := counts[x] + 1;
        i := i + 1;
    }

    p := 0;
    i := 0;
    // Buggy loop: iterates over 'arr' (input array) instead of 'counts'
    // This matches the Python: for i, count in enumerate(arr):
    // and Java: for (Integer count : arr)
    while (i < n)
        invariant 0 <= i && i <= n;
        invariant p >= 0;
    {
        count := arr[i]; // The bug: treating input values as counts
        j := 0;
        // In the buggy program, 'count' comes from 'arr[i]', which is < k.
        // But 'count' represents a number of elements to add.
        // It could be 0.
        while (j < count)
            invariant 0 <= j && j <= (if count >= 0 then count else 0);
            invariant p >= 0; 
        {
            sorted_arr[p] := i;
            p := p + 1;
            j := j + 1;
        }
        i := i + 1;
    }
}
