type Node;
function successor(Node) : Node;
const Null: Node;

function Reachable(start: Node, end: Node) : bool;
axiom (forall n: Node :: Reachable(n, n));
axiom (forall n: Node :: n != Null ==> Reachable(n, successor(n)));
axiom (forall n, m: Node :: {Reachable(n, m)} Reachable(n, m) && m != Null ==> Reachable(n, successor(m)));

procedure detect_cycle(startnode: Node) returns (result: bool)
    ensures result ==> (exists n: Node :: n != Null && Reachable(startnode, n) && Reachable(successor(n), n));
{
    var tortoise, hare: Node;
    tortoise := startnode;
    hare := startnode;

    while (true)
    {
        if (hare == Null || successor(hare) == Null)
        {
            result := false;
            return;
        }

        tortoise := successor(tortoise);
        hare := successor(successor(hare));

        if (tortoise == hare)
        {
            result := true;
            return;
        }
    }
}
