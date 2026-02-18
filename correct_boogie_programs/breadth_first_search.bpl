type Node;
function Successors(n: Node, i: int) : Node;
function NumSuccessors(n: Node) : int;

axiom (forall n: Node :: NumSuccessors(n) >= 0);

function Reachable(start: Node, end: Node) : bool;

axiom (forall n: Node :: Reachable(n, n));
axiom (forall n: Node, i: int :: 0 <= i && i < NumSuccessors(n) ==> Reachable(n, Successors(n, i)));
axiom (forall n, m, k: Node :: Reachable(n, m) && Reachable(m, k) ==> Reachable(n, k));

// Induction axiom for completeness
axiom (forall start: Node, target: Node, V: [Node]bool :: 
    (V[start] && (forall n: Node, i: int :: (V[n] && 0 <= i && i < NumSuccessors(n)) ==> V[Successors(n, i)]) && Reachable(start, target)) 
    ==> V[target]);

procedure breadth_first_search(startnode: Node, goalnode: Node) returns (result: bool)
    ensures result <==> Reachable(startnode, goalnode);
{
    var visited: [Node]bool;
    var pos: [Node]int;
    var queue: [int]Node;
    var head, tail: int;
    var node, s: Node;
    var i_succ: int;

    visited := (lambda n: Node :: false);
    visited[startnode] := true;
    pos[startnode] := 0;
    head := 0;
    tail := 0;
    queue[tail] := startnode;
    tail := tail + 1;

    while (head < tail)
        invariant 0 <= head && head <= tail;
        invariant (forall k: int :: 0 <= k && k < tail ==> Reachable(startnode, queue[k]));
        invariant (forall n: Node :: visited[n] ==> Reachable(startnode, n));
        invariant visited[startnode];
        invariant (forall k: int :: 0 <= k && k < head ==> queue[k] != goalnode);
        invariant (forall n: Node :: visited[n] ==> 0 <= pos[n] && pos[n] < tail && queue[pos[n]] == n);
        invariant (forall k: int, idx: int :: (0 <= k && k < head && 0 <= idx && idx < NumSuccessors(queue[k])) ==> visited[Successors(queue[k], idx)]);
    {
        node := queue[head];
        
        if (node == goalnode) {
            result := true;
            return;
        }

        i_succ := 0;
        while (i_succ < NumSuccessors(node))
            invariant 0 <= i_succ && i_succ <= NumSuccessors(node);
            invariant 0 <= head && head < tail;
            invariant node == queue[head];
            invariant (forall k: int :: 0 <= k && k < tail ==> Reachable(startnode, queue[k]));
            invariant (forall n: Node :: visited[n] ==> Reachable(startnode, n));
            invariant visited[startnode];
            invariant (forall k: int :: 0 <= k && k <= head ==> queue[k] != goalnode);
            invariant (forall n: Node :: visited[n] ==> 0 <= pos[n] && pos[n] < tail && queue[pos[n]] == n);
            invariant (forall k: int, idx: int :: (0 <= k && k < head && 0 <= idx && idx < NumSuccessors(queue[k])) ==> visited[Successors(queue[k], idx)]);
            invariant (forall idx: int :: 0 <= idx && idx < i_succ ==> visited[Successors(node, idx)]);
        {
            s := Successors(node, i_succ);
            if (!visited[s])
            {
                queue[tail] := s;
                pos[s] := tail;
                visited[s] := true;
                tail := tail + 1;
            }
            i_succ := i_succ + 1;
        }
        
        head := head + 1;
    }
    assert !visited[goalnode];
    assert (forall n: Node, i: int :: (visited[n] && 0 <= i && i < NumSuccessors(n)) ==> visited[Successors(n, i)]);
    result := false;
}
