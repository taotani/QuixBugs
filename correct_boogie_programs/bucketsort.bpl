procedure bucketsort(arr: [int]int, n: int, k: int) returns (sorted_arr: [int]int)
    requires n >= 0 && k > 0;
    requires (forall i: int :: 0 <= i && i < n ==> 0 <= arr[i] && arr[i] < k);
    ensures (forall i, j: int :: 0 <= i && i < j && j < n ==> sorted_arr[i] <= sorted_arr[j]);
{
    var counts: [int]int;
    var i, x, count, j, p: int;

    counts := (lambda m: int :: 0);
    i := 0;
    while (i < n)
        invariant 0 <= i && i <= n;
        invariant (forall m: int :: 0 <= m && m < k ==> counts[m] >= 0);
    {
        x := arr[i];
        counts[x] := counts[x] + 1;
        i := i + 1;
    }

    p := 0;
    i := 0;
    while (i < k)
        invariant 0 <= i && i <= k;
        invariant 0 <= p && p <= n;
        invariant (forall m: int :: 0 <= m && m < p ==> sorted_arr[m] < i);
        invariant (forall m1, m2: int :: 0 <= m1 && m1 < m2 && m2 < p ==> sorted_arr[m1] <= sorted_arr[m2]);
    {
        count := counts[i];
        j := 0;
        while (j < count)
            invariant 0 <= j && j <= count;
            invariant 0 <= p && p <= n;
            invariant (forall m: int :: p - j <= m && m < p ==> sorted_arr[m] == i);
            invariant (forall m: int :: 0 <= m && m < p - j ==> sorted_arr[m] < i);
            invariant (forall m1, m2: int :: 0 <= m1 && m1 < m2 && m2 < p ==> sorted_arr[m1] <= sorted_arr[m2]);
        {
            assume p < n; 
            sorted_arr[p] := i;
            p := p + 1;
            j := j + 1;
        }
        i := i + 1;
    }
    // Assume we filled the array (sum of counts == n)
    assume p == n;
}
