-- Sum test
-- ==
--input { [4u32,3u32,2u32,1u32] }
-- output { 10u32 }

let addU32 (i : u32) (j : u32) = i + j
let subU32 (i : u32) (j : u32) = i - j
let multU32 (i : u32) (j : u32) = i * j
let eqU32 (a : u32 ) (b : u32 ) = a == b
let lebU32 (a : u32 ) (b : u32 ) = a <= b
let ltbU32 (a : u32 ) (b : u32 ) = a < b

let sum (xs : [] u32) = reduce addU32 0 xs

let main = sum
