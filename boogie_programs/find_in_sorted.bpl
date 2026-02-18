function FindInSorted(arr: [int]int, x: int, start: int, end: int) : int;
axiom (forall arr: [int]int, x: int, start: int, end: int :: 
    FindInSorted(arr, x, start, end) == 
    (if start == end then -1 else 
        (if x < arr[start + (end - start) div 2] then FindInSorted(arr, x, start, start + (end - start) div 2) else
            (if x > arr[start + (end - start) div 2] then FindInSorted(arr, x, start + (end - start) div 2, end) else
                start + (end - start) div 2))));

procedure find_in_sorted(arr: [int]int, x: int, start: int, end: int) returns (index: int)
    requires (forall i, j: int :: start <= i && i < j && j < end ==> arr[i] <= arr[j]);
    ensures index == FindInSorted(arr, x, start, end);
{
    var mid: int;
    if (start == end) {
        index := -1;
    } else {
        mid := start + (end - start) div 2;
        if (x < arr[mid]) {
            call index := find_in_sorted(arr, x, start, mid);
        } else if (x > arr[mid]) {
            call index := find_in_sorted(arr, x, mid, end);
        } else {
            index := mid;
        }
    }
}
