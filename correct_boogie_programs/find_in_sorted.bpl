procedure find_in_sorted(arr: [int]int, x: int, start: int, end: int) returns (index: int)
    requires (forall i: int, j: int :: start <= i && i < j && j < end ==> arr[i] <= arr[j]);
    ensures (index == -1 ==> (forall i: int :: start <= i && i < end ==> arr[i] != x));
    ensures (index != -1 ==> start <= index && index < end && arr[index] == x);
{
    var mid: int;
    if (start == end) {
        index := -1;
    } else {
        mid := start + (end - start) div 2;
        if (x < arr[mid]) {
            call index := find_in_sorted(arr, x, start, mid);
        } else if (x > arr[mid]) {
            call index := find_in_sorted(arr, x, mid + 1, end);
        } else {
            index := mid;
        }
    }
}
