function {:builtin "bvand"} bvand(bv32, bv32) : bv32;
function {:builtin "bvsub"} bvsub(bv32, bv32) : bv32;

function PopCount(b: bv32) : int;
axiom PopCount(0bv32) == 0;
axiom (forall b: bv32 :: b != 0bv32 ==> PopCount(b) == 1 + PopCount(bvand(b, bvsub(b, 1bv32))));

procedure bitcount(n_in: bv32) returns (count: int)
    requires true;
    ensures count == PopCount(n_in);
{
    var n: bv32;
    n := n_in;
    count := 0;
    while (n != 0bv32)
        invariant count + PopCount(n) == PopCount(n_in);
    {
        n := bvand(n, bvsub(n, 1bv32));
        count := count + 1;
    }
}
