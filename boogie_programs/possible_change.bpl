procedure possible_change(coins: [int]int, i: int, n_coins: int, total: int) returns (count: int)
{
    var res1, res2: int;

    if (total == 0)
    {
        count := 1;
        return;
    }
    if (total < 0)
    {
        count := 0;
        return;
    }

    call res1 := possible_change(coins, i, n_coins, total - coins[i]);
    call res2 := possible_change(coins, i + 1, n_coins, total);
    count := res1 + res2;
}
