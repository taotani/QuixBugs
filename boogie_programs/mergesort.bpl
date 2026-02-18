procedure merge(left: [int]int, n_left: int, right: [int]int, n_right: int) returns (result: [int]int);
    ensures (forall i, j: int :: 0 <= i && i < j && j < n_left + n_right ==> result[i] <= result[j]);

procedure mergesort(arr: [int]int, n: int) returns (result: [int]int)
    ensures (forall i, j: int :: 0 <= i && i < j && j < n ==> result[i] <= result[j]);
{
    var middle: int;
    var left, right: [int]int;
    var res_left, res_right: [int]int;
    var i: int;

    if (n == 0)
    {
        result := arr;
    }
    else
    {
        middle := n div 2;
        i := 0;
        while (i < middle)
            invariant 0 <= i && i <= middle;
        {
            left[i] := arr[i];
            i := i + 1;
        }
        i := 0;
        while (i < n - middle)
            invariant 0 <= i && i <= n - middle;
        {
            right[i] := arr[i + middle];
            i := i + 1;
        }

        call res_left := mergesort(left, middle);
        call res_right := mergesort(right, n - middle);
        call result := merge(res_left, middle, res_right, n - middle);
    }
}
