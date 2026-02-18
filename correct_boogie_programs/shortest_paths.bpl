procedure shortest_paths(source: int, n: int, edges_u: [int]int, edges_v: [int]int, edges_w: [int]int, n_edges: int) returns (weight_by_node: [int]int)
{
    var i, j, u, v, w, update_weight: int;
    var INF: int;
    INF := 99999;

    i := 0;
    while (i < n)
        invariant 0 <= i && i <= n;
    {
        weight_by_node[i] := INF;
        i := i + 1;
    }
    weight_by_node[source] := 0;

    i := 0;
    while (i < n)
        invariant 0 <= i && i <= n;
    {
        j := 0;
        while (j < n_edges)
            invariant 0 <= j && j <= n_edges;
        {
            u := edges_u[j];
            v := edges_v[j];
            w := edges_w[j];
            
            update_weight := (if weight_by_node[u] + w < weight_by_node[v] then weight_by_node[u] + w else weight_by_node[v]);
            weight_by_node[v] := update_weight;
            j := j + 1;
        }
        i := i + 1;
    }
}
