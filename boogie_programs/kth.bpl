procedure kth(arr: [int]int, n: int, k: int) returns (result: int)
    requires 0 <= k && k < n;
{
    var pivot, i, x: int;
    var below, above: [int]int;
    var n_below, n_above: int;
    var num_less, num_lessoreq: int;

    pivot := arr[0];
    n_below := 0;
    n_above := 0;
    i := 0;
    while (i < n)
        invariant 0 <= i && i <= n;
    {
        x := arr[i];
        if (x < pivot)
        {
            below[n_below] := x;
            n_below := n_below + 1;
        }
        else if (x > pivot)
        {
            above[n_above] := x;
            n_above := n_above + 1;
        }
        i := i + 1;
    }

    num_less := n_below;
    num_lessoreq := n - n_above;

    if (k < num_less)
    {
        call result := kth(below, n_below, k);
    }
    else if (k >= num_lessoreq)
    {
        call result := kth(above, n_above, k);
    }
    else
    {
        result := pivot;
    }
}
