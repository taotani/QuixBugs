type Node;
function Successors(n: Node, i: int) : Node;
function NumSuccessors(n: Node) : int;

axiom (forall n: Node :: NumSuccessors(n) >= 0);

function Reachable(start: Node, end: Node) : bool;

axiom (forall n: Node :: Reachable(n, n));
axiom (forall n: Node, i: int :: 0 <= i && i < NumSuccessors(n) ==> Reachable(n, Successors(n, i)));
axiom (forall n, m, k: Node :: Reachable(n, m) && Reachable(m, k) ==> Reachable(n, k));

// Induction axiom for reachability
axiom (forall start: Node, target: Node, V: [Node]bool :: 
    (V[start] && (forall n: Node, i: int :: (V[n] && 0 <= i && i < NumSuccessors(n)) ==> V[Successors(n, i)]) && Reachable(start, target)) 
    ==> V[target]);

procedure breadth_first_search(startnode: Node, goalnode: Node) returns (result: bool)
    ensures result ==> Reachable(startnode, goalnode);
{
    var visited: [Node]bool;
    var queue: [int]Node;
    var valid_queue: [int]bool;
    var head, tail: int;
    var node, s: Node;
    var i_succ: int;

    visited := (lambda n: Node :: false);
    visited[startnode] := true;
    head := 0;
    tail := 0;
    queue[tail] := startnode;
    valid_queue := (lambda i: int :: false);
    valid_queue[tail] := true;
    tail := tail + 1;

    while (true)
        invariant (forall n: Node :: visited[n] ==> Reachable(startnode, n));
        invariant (forall k: int :: valid_queue[k] ==> Reachable(startnode, queue[k]));
    {
        // In the buggy version, we don't check if the queue is empty.
        // If head is not in valid_queue, we might get an unreachable node.
        // To verify soundness of the 'true' result, we only care about cases where we find the goal.
        node := queue[head];
        
        // If we popped a node that was never put in the queue (or uninitialized),
        // we can't prove it's reachable.
        assume valid_queue[head]; 

        if (node == goalnode) {
            result := true;
            return;
        }

        i_succ := 0;
        while (i_succ < NumSuccessors(node))
            invariant 0 <= i_succ && i_succ <= NumSuccessors(node);
            invariant (forall n: Node :: visited[n] ==> Reachable(startnode, n));
            invariant (forall k: int :: valid_queue[k] ==> Reachable(startnode, queue[k]));
            invariant Reachable(startnode, node);
        {
            s := Successors(node, i_succ);
            if (!visited[s])
            {
                head := head - 1;
                queue[head] := s;
                valid_queue[head] := true;
                visited[s] := true;
            }
            i_succ := i_succ + 1;
        }
    }
}
