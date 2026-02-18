type Node;
const Null: Node;
var Successor: [Node]Node;

function Reachable(S: [Node]Node, start: Node, end: Node) : bool;

procedure reverse_linked_list(startnode: Node) returns (new_head: Node)
    modifies Successor;
    // Buggy specification: it just sets everything to Null
    ensures (forall n: Node :: Reachable(old(Successor), startnode, n) && n != Null ==> Successor[n] == Null);
{
    var node, prevnode, nextnode: Node;
    node := startnode;
    prevnode := Null;
    while (node != Null)
        invariant (forall m: Node :: Reachable(old(Successor), startnode, m) && !Reachable(old(Successor), node, m) && m != Null ==> Successor[m] == Null);
    {
        nextnode := Successor[node];
        Successor[node] := prevnode;
        node := nextnode;
    }
    new_head := prevnode;
}
