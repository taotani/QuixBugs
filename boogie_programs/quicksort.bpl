procedure quicksort(arr: [int]int, n: int) returns (result: [int]int)
    ensures (forall i, j: int :: 0 <= i && i < j && j < n ==> result[i] <= result[j]);
{
    var pivot, i, x: int;
    var lesser, greater: [int]int;
    var n_lesser, n_greater: int;
    var res_lesser, res_greater: [int]int;

    if (n <= 1)
    {
        result := arr;
    }
    else
    {
        pivot := arr[0];
        n_lesser := 0;
        n_greater := 0;
        i := 1;
        while (i < n)
            invariant 1 <= i && i <= n;
        {
            x := arr[i];
            if (x < pivot)
            {
                lesser[n_lesser] := x;
                n_lesser := n_lesser + 1;
            }
            else if (x > pivot)
            {
                greater[n_greater] := x;
                n_greater := n_greater + 1;
            }
            i := i + 1;
        }

        call res_lesser := quicksort(lesser, n_lesser);
        call res_greater := quicksort(greater, n_greater);

        i := 0;
        while (i < n_lesser)
            invariant 0 <= i && i <= n_lesser;
        {
            result[i] := res_lesser[i];
            i := i + 1;
        }
        result[n_lesser] := pivot;
        i := 0;
        while (i < n_greater)
            invariant 0 <= i && i <= n_greater;
        {
            result[n_lesser + 1 + i] := res_greater[i];
            i := i + 1;
        }
    }
}
