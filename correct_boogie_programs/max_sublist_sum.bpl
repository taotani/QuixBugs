function max(a: int, b: int) : int { if a > b then a else b }
function Sum(arr: [int]int, i: int, j: int) : int;
axiom (forall arr: [int]int, i: int :: Sum(arr, i, i) == 0);
axiom (forall arr: [int]int, i: int, j: int :: i <= j ==> Sum(arr, i, j + 1) == Sum(arr, i, j) + arr[j]);

procedure max_sublist_sum(arr: [int]int, n: int) returns (max_so_far: int)
    requires n >= 0;
    ensures (forall i: int, j: int :: 0 <= i && i <= j && j <= n ==> max_so_far >= Sum(arr, i, j));
    ensures (exists i: int, j: int :: 0 <= i && i <= j && j <= n && max_so_far == Sum(arr, i, j));
{
    var max_ending_here: int;
    var i: int;
    max_ending_here := 0;
    max_so_far := 0;
    i := 0;
    while (i < n)
        invariant 0 <= i && i <= n;
        invariant (forall j: int :: 0 <= j && j <= i ==> max_ending_here >= Sum(arr, j, i));
        invariant (exists j: int :: 0 <= j && j <= i && max_ending_here == Sum(arr, j, i));
        invariant (forall j: int, k: int :: 0 <= j && j <= k && k <= i ==> max_so_far >= Sum(arr, j, k));
    {
        max_ending_here := max(0, max_ending_here + arr[i]);
        max_so_far := max(max_so_far, max_ending_here);
        i := i + 1;
    }
}
