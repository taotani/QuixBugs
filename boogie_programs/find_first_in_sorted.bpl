procedure find_first_in_sorted(arr: [int]int, n: int, x: int) returns (index: int)
    requires n >= 0;
    requires (forall i, j: int :: 0 <= i && i < j && j < n ==> arr[i] <= arr[j]);
    ensures (index == -1 ==> (forall i: int :: 0 <= i && i < n ==> arr[i] != x));
    ensures (index != -1 ==> 0 <= index && index < n && arr[index] == x && (index == 0 || arr[index - 1] != x));
{
    var lo, hi, mid: int;
    lo := 0;
    hi := n;
    while (lo <= hi)
    {
        mid := (lo + hi) div 2;
        if (x == arr[mid] && (mid == 0 || x != arr[mid - 1]))
        {
            index := mid;
            return;
        }
        else if (x <= arr[mid])
        {
            hi := mid;
        }
        else
        {
            lo := mid + 1;
        }
    }
    index := -1;
}
