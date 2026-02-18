function min(a: int, b: int) : int { if a < b then a else b }

procedure levenshtein(source: [int]int, i: int, n_s: int, target: [int]int, j: int, n_t: int) returns (distance: int)
    requires 0 <= i && i <= n_s;
    requires 0 <= j && j <= n_t;
{
    var d1, d2, d3: int;
    if (i == n_s || j == n_t)
    {
        distance := (if i == n_s then n_t - j else n_s - i);
    }
    else if (source[i] == target[j])
    {
        call distance := levenshtein(source, i + 1, n_s, target, j + 1, n_t);
    }
    else
    {
        call d1 := levenshtein(source, i, n_s, target, j + 1, n_t);
        call d2 := levenshtein(source, i + 1, n_s, target, j + 1, n_t);
        call d3 := levenshtein(source, i + 1, n_s, target, j, n_t);
        distance := 1 + min(d1, min(d2, d3));
    }
}
