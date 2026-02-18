type Node;
function Successors(Node) : [Node]bool;
function Predecessors(Node) : [Node]bool;

procedure topological_ordering(nodes: [int]Node, n: int) returns (ordered_nodes: [int]Node, n_ordered: int)
{
    var i, j, k: int;
    var node, nextNode: Node;
    var visited: [Node]bool;
    var in_ordered: [Node]bool;
    var cond: bool;

    n_ordered := 0;
    i := 0;
    while (i < n)
    {
        node := nodes[i];
        havoc cond;
        assume cond <==> (forall m: Node :: !Predecessors(node)[m]);
        if (cond)
        {
            ordered_nodes[n_ordered] := node;
            in_ordered[node] := true;
            n_ordered := n_ordered + 1;
        }
        i := i + 1;
    }

    i := 0;
    while (i < n_ordered)
    {
        node := ordered_nodes[i];
        while (*)
        {
            havoc nextNode;
            if (Successors(node)[nextNode] && !in_ordered[nextNode])
            {
                havoc cond;
                assume cond <==> (forall m: Node :: Successors(nextNode)[m] ==> in_ordered[m]);
                if (cond)
                {
                    ordered_nodes[n_ordered] := nextNode;
                    in_ordered[nextNode] := true;
                    n_ordered := n_ordered + 1;
                }
            }
            else
            {
                break;
            }
        }
        i := i + 1;
    }
}
