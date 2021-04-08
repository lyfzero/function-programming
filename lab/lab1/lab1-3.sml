(* zip: string list * int list -> (string * int) list
   REQUIRES: 
   ENSURES: 
*)
fun zip ([], _) : (string * int) list = []
  | zip (_, []) = []
  | zip (s::sl, n::il) = (s, n)::zip(sl, il);
(* Testcase *)
val [("hello", 1), ("world", 2)] = zip (["hello", "world"], [1,2,3]);
val [("hello", 1), ("world", 2)] = zip (["hello", "world", "lyf"], [1,2]);
val [] = zip ([], []);

(* unzip: (string * int) list -> string list * int list
   REQUIRES:
   ENSURES:
*)
fun unzip ([]) : string list * int list = ([], [])
  | unzip ((s, n)::L) = let val (sl, il) = unzip(L) 
    in (s::sl, n::il)
    end;
(* Testcase *)
val (["hello", "world"], [1, 2]) = unzip [("hello", 1), ("world", 2)];
val ([], []) = unzip [];

fun unzip l : string list * int list = 
  case l of 
    [] => ([], [])
    | (s,n)::tl => let val (sl, il) = unzip tl
        in (s::sl, n::il) end

val (["hello", "world"], [1, 2]) = unzip [("hello", 1), ("world", 2)];
val ([], []) = unzip [];