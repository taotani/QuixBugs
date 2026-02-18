type Node;
const Null: Node;
var Successor: [Node]Node;

procedure reverse_linked_list(startnode: Node) returns (new_head: Node)
    modifies Successor;
{
    var node, prevnode, nextnode: Node;
    node := startnode;
    prevnode := Null;
    while (node != Null)
    {
        nextnode := Successor[node];
        Successor[node] := prevnode;
        prevnode := node;
        node := nextnode;
    }
    new_head := prevnode;
}
