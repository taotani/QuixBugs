function GCD(a: int, b: int) : int;
// Buggy axiom: matches the buggy implementation's recursive call
axiom (forall a: int, b: int :: a >= 0 && b >= 0 ==> GCD(a, b) == (if b == 0 then a else GCD(a mod b, b)));

procedure gcd(a: int, b: int) returns (result: int)
    requires a >= 0 && b >= 0;
    ensures result == GCD(a, b);
{
    if (b == 0) {
        result := a;
    } else {
        call result := gcd(a mod b, b);
    }
}
