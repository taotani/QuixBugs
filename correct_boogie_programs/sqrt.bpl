function abs(r: real) : real { if r >= 0.0 then r else -r }

procedure sqrt(x: real, epsilon: real) returns (approx: real)
    requires x >= 1.0 && epsilon > 0.0;
    ensures abs(x - approx * approx) <= epsilon;
{
    approx := x / 2.0;
    while (abs(x - approx * approx) > epsilon)
    {
        approx := 0.5 * (approx + x / approx);
    }
}
