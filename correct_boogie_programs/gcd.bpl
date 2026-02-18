function GCD(a: int, b: int) : int;
axiom (forall a: int, b: int :: a >= 0 && b >= 0 ==> GCD(a, b) == (if b == 0 then a else GCD(b, a mod b)));

procedure gcd(a: int, b: int) returns (result: int)
    requires a >= 0 && b >= 0;
    ensures result == GCD(a, b);
{
    if (b == 0) {
        result := a;
    } else {
        call result := gcd(b, a mod b);
    }
}
