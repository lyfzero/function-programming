(* lab 2-1-1*)
(* reverse int list -> int list
   REQUIRES: true
   ENSURES: reverse(L) reverse a list without helper function
*)
fun reverse ([]) : int list = []
  | reverse (x::L : int list) = reverse (L) @ [x];
(* Testcase *)
val [5, 4, 3, 2, 1] = reverse [1, 2, 3, 4, 5];
val [] = reverse [];

(* lab 2-1-2*)
(* reverse_helper int list * int list -> int list
   REQUIRES: true
   ENSURES: store result of reversed L into RL
*)
fun reverse_helper ([], RL) = RL
  | reverse_helper (x::L, RL) = reverse_helper (L, x::RL);
(* reverse' int list -> int list
   REQUIRES: true
   ENSURES: reverse'(L) reverse a list with helper function, complexity O(n)
*)
fun reverse' (L: int list) : int list = reverse_helper (L, []);
(* Testcase *)
val [5, 4, 3, 2, 1] = reverse' [1, 2, 3, 4, 5];
val [] = reverse' [];


(* lab 2-2 *)
(* interleave: int list * int list -> int list
   REQUIRES: true
   ENSURES: merge two list one by one
*)
fun interleave ([], LB : int list) : int list = LB
  | interleave (LA : int list, []) = LA
  | interleave (x::LA, y::LB) = x::y::interleave(LA, LB);
(* Testcase *)
val [2, 4] = interleave([2], [4])
val [2, 4, 3 ,5] = interleave([2, 3], [4, 5]);
val [2, 4, 3, 5, 6, 7, 8, 9] = interleave([2, 3], [4, 5, 6, 7, 8, 9])
val [2, 3] = interleave([2, 3], [])



datatype tree = Empty | Node of tree * int * tree;
(* Ins: int * tree -> tree
   REQUIRES: true
   ENSURES: insert a node x to a sortedTree
*)
fun Ins(x, Empty) = Node(Empty, x, Empty)
  | Ins(x, Node(left, root, right)) = 
        case Int.compare(x, root) of
            LESS => Node(Ins(x, left), root, right)
          | _ => Node(left, root, Ins(x, right));  
(* trav: tree -> int list
   REQUIRES: true
   ENSURES: traverse a tree in inorder 
*)
fun trav (Empty) = []
  | trav (Node(left, root, right)) = trav(left) @ (root::(trav(right)));

(* lab 2-3 *)
(* split: 
   REQUIRES: true
   ENSURES:split L to (L1, x, L2) with L = L1 @ x::L2 and |length(L1) - length(L2)| < 1
*)
fun split ([]) = ([], 0, [])
  | split ([x]) = ([], x, [])
  | split (x::L) = 
        let
            val (left, root, right) = split L
        in 
            if length(left) > length(right)
            then (left, x, root::right)
            else (root::left, x, right)
        end;
(* listToTree: int list -> tree
   REQUIRES: true
   ENSURES: converse a tab to a AVL tree
*)
fun listToTree ([]) = Empty
  | listToTree ([x]) = Node(Empty, x, Empty)
  | listToTree (L) = 
        let 
            val (left, root, right) = split (L)
        in
            Node(listToTree(left), root, listToTree(right))
        end;
(* Testcase *)
val list1 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
val tree1 = listToTree list1;
trav tree1;

(* lab 2-4 *)
(* revT: tree -> tree
   REQUIRES: a binary ALV tree
   ENSURES: trav(revT t) = reverse(trav t)
*)
fun revT (Empty) = Empty
  | revT (Node(left, root, right)) = Node(revT (right), root, revT (left));
(* Testcase *)
trav(revT tree1) = reverse(trav tree1);

(* lab 2-5 *)
(* binarySearch: tree * int -> bool
   ENQUIRES:
   ENSURES:
*)
fun binarySearch (Empty, _) = false
  | binarySearch (Node(left, root, right), x) = 
        case Int.compare(x, root) of
            LESS => binarySearch(left, x)
          | EQUAL => true
          | GREATER => binarySearch(right, x);
(* Testcase *)
fun createSortedTree [] = Empty
  | createSortedTree (x::L) = Ins(x, createSortedTree(L));
val sortedTree = createSortedTree ([9, 8, 7, 6, 5, 4, 3, 2, 1]);
val false = binarySearch(sortedTree, 0);
val true = binarySearch(sortedTree, 9);
val true = binarySearch(sortedTree, 4);
val false = binarySearch(sortedTree, 10);
