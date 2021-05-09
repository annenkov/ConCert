let addI32 (i : i32) (j : i32) = i + j
let subI32 (i : i32) (j : i32) = i - j
let multI32 (i : i32) (j : i32) = i * j
let divI32 (i : i32) (j : i32) = i / j
let leI32 (i : i32) (j : i32) = i <= j
let ltI32 (i : i32) (j : i32) = i < j
let eqI32 (i : i32) (j : i32) = i == j

let dotprod (xs : [] i32) (ys : [] i32) = reduce addI32 0i32 (map2 multI32 xs ys)

let dotprod_list_of_pairs (xs : [] (i32,i32)) = let pair_of_lists = unzip xs in
dotprod pair_of_lists.0 pair_of_lists.1

let main = dotprod_list_of_pairs [ (1,4), (2,-5), (3,6) ]
