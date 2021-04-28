(* lab 3-1 *)
(* thenAddOne: ((int -> int) * int) -> int
   REQUIRES: true
   ENSURES: evaluate a integer to function f then add one
*)
fun thenAddOne (f : int->int, x : int) : int = f (x) + 1;
(* Testcase *)
val square = fn (x : int) => x * x;
val 17 = thenAddOne (square, 4);
val double = fn (x : int) => 2 * x;
val 9 = thenAddOne (double, 4);


(* lab 3-2-1 *)
(* mapList: (('a -> 'b) * 'a list) -> 'b list
   REQUIRES: true
   ENSURES: map function f to a list
*)
fun mapList (f, []) = []
  | mapList (f, x :: L) = f (x) :: mapList (f, L);
(* Testcase *)
val [2, 4, 8] = mapList (double, [1, 2, 4]);
val [1, 4, 16] = mapList (square, [1, 2, 4]);


(* lab 3-2-2 *)
(* mapList': ('a -> 'b) -> ('a list -> 'b list)
   REQUIRES: true
   ENSURES: map function f to a list
*)
fun mapList' (f) = 
  fn (L) => case L of
       [] => []
    |  x::R => f (x) :: (mapList' f) R;
(* Testcase *)
val [2, 4, 8] = (mapList' double) [1, 2, 4];
val [1, 4, 16] = (mapList' square) [1, 2, 4];

(* lab 3-3 *)
(* findOdd: int list -> int option
   REQUIRES: true
   ENSURES: if x is the first odd in L, return SOME x; else return NONE;
*)
fun findOdd ([]) = NONE
  | findOdd (x::L) = 
        if (x mod 2) = 1 then SOME x
        else findOdd L;
(* Testcase *)
val SOME 1 = findOdd ([1, 2, 3, 4, 5]);
val NONE = findOdd ([2, 4, 6, 8, 10]);

(* lab 3-4 *)
(* treeFilter: ('a -> bool') -> 'a tree -> 'a option tree
   REQUIRES: true
   ENSURES: replace the node in tree with option
*)
datatype 'a tree = Empty | Node of 'a tree * 'a * 'a tree;
fun treeFilter (f, Empty) = Empty
  | treeFilter (f, Node(left, root, right)) = 
        if (f (root)) then 
            Node(treeFilter (f, left), SOME root, treeFilter (f, right))
        else 
            Node(treeFilter (f, left), NONE, treeFilter (f, right));
(* Testcase *)
val aboveZero = fn x => x > 0;
val tree1 = Node(Node(Empty, 5, Empty), ~3, Node(Empty, 1, Empty));
val tree2 = Node(Node(Empty, SOME 5, Empty), NONE, Node(Empty, SOME 1, Empty))
val tree2 = treeFilter (aboveZero, tree1);

(* lab 3-5 *)
datatype tree = Node of tree * int * tree  | Empty
(* treecompare: tree * tree -> order 
   REQUIRES: true
   ENSURES: when given two trees, returns a value of type order, 
   based on which tree has a largervalue at the root node 
*) 
fun treecompare(Empty : tree, Empty : tree) : order = EQUAL
  | treecompare(Empty, _) = GREATER
  | treecompare(_, Empty) = LESS
  | treecompare(Node(_, root1, _), Node(_, root2, _)) = Int.compare(root1, root2);
(* Testcase *)
val GREATER = treecompare(Node(Empty, 5, Empty), Node(Empty, 2, Empty))
val LESS = treecompare(Node(Empty, 2, Empty), Node(Empty, 6, Empty))
val EQUAL = treecompare(Node(Empty, 3, Empty), Node(Node(Empty, 5, Empty), 3, Empty))

(* SwapDown: tree -> tree
   REQUIRES: the subtrees of t are both minheaps
   ENSURES: swapDown(t) = if t is Empty or all of t’s immediate children are empty then
   just return t, otherwise returns a minheap which contains exactly the elements in t. 
*) 
fun swapDown (Empty : tree) : tree = Empty
  | swapDown(T as Node(left, root, right)) = 
        let 
            val (smallTree, bigTree) = 
                case treecompare(left, right) of 
                    GREATER => (right, left)
                    | _ => (left, right)
        in 
            case smallTree of
                Empty => Node(smallTree, root, bigTree)
              | Node(smallLeft, smallRoot, smallRight) => 
                    (case treecompare(T, smallTree) of
                          GREATER => Node(swapDown(Node(smallLeft, root, smallRight)), smallRoot, bigTree)
                        | _ => T)
        end;
(* Testcase *)
val Node(Node(Empty, 3, Empty), 2, Node(Empty, 4, Empty)) =
    swapDown(Node(Node(Empty, 4, Empty), 3, Node(Empty, 2, Empty)))
val Empty = swapDown(Empty)
(* heapify : tree -> tree
   REQUIRES: tree
   ENSURES: given an arbitrary tree t, evaluates to a minheap with exactly the elements of t.  
*)
fun heapify(Empty : tree) : tree = Empty
  | heapify(Node(left, root, right)) = swapDown(Node(heapify(left), root, heapify(right)));

val Node(Node(Empty, 4, Empty), 2, Empty) = heapify(Node(Node(Empty, 2, Empty), 4, Empty))
val Empty = heapify Empty