type Node;
function Successors(Node) : [Node]bool;
function Reachable(start: Node, end: Node) : bool;

var visited: [Node]bool;

procedure depth_first_search(startnode: Node, goalnode: Node) returns (result: bool)
    modifies visited;
    ensures result ==> Reachable(startnode, goalnode);
{
    visited := (lambda n: Node :: false);
    call result := search(startnode, goalnode);
}

procedure search(node: Node, goalnode: Node) returns (found: bool)
    modifies visited;
{
    var s: Node;
    if (visited[node])
    {
        found := false;
        return;
    }
    if (node == goalnode)
    {
        found := true;
        return;
    }

    while (*)
    {
        havoc s;
        if (Successors(node)[s])
        {
            call found := search(s, goalnode);
            if (found) { return; }
        }
        else
        {
            break;
        }
    }
    found := false;
}
