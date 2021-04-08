(* lab 1-2*)
(* mult int list -> int
   REQUIRES: true
   ENSURES: mult(L) evaluates to the product of the integers in L
*)
fun mult [] = 1
  | mult (x::L) = x * mult(L);
(* Testcase *)
val 120 = mult [1, 2, 3, 4, 5];
val 1 = mult [];
val 2 = mult [1, 2];


(* lab 1-3*)
(* Mult: int list list -> int
   REQUIRES: true
   ENSURES: Mult(R) evaluates to the product of all the integers in the lists of R
*)
fun Mult [] = 1
  | Mult (r::R) = mult(r) * Mult(R);
(* Testcase *)
val 120 = Mult [[1, 2], [3, 4], [5]];
val 1 = Mult [];
val 1 = Mult [[], []];
val 1 = Mult [[1], [1]];
val 2 = Mult [[1], [2]];


(* lab 1-4-1 *)
(* mult': int list * int -> int
   REQUIRES: true
   ENSURES: mult'(L, a) evaluate to the product of the integers in L and a
*)
fun mult' ([], a) = a
  | mult' (x::L, a) = mult' (L, x * a);
(* Testcase *)
val 120 = mult' ([1, 2, 3, 4, 5], 1);
val 1 = mult' ([], 1);
val 2 = mult' ([1, 2], 1);

(* lab 1-4-2 *)
(* Mult': int list list * int -> int
   REQUIRES: true
   ENSURES: Mult'(R, a) evaluate to the product of al the intergers in the lists of R and a
*)
fun Mult'([], a) = a
  | Mult' (r::R, a) = Mult'(R, 1) * mult'(r, a);
(* Testcase *)
val 120 = Mult' ([[1, 2], [3, 4], [5]], 1);
val 1 = Mult' ([], 1);
val 1 = Mult' ([[], []], 1);
val 1 = Mult' ([[1], [1]], 1);
val 2 = Mult' ([[1], [2]], 1);


(* lab 1-5 *)
(* double: int -> int
   REQUIRES: n >= 0
   ENSURES: double n evaluates to 2 * n 
*)
fun double (0 : int): int = 0
  | double n = 2 + double (n - 1);
(* square: int -> int
   REQUIRES: n >= 0
   ENSURES: square n evaluates to n * n
*)
fun square (0 : int): int = 0
  | square(x) = square(x - 1) + double(x - 1) + 1;
(* Testcase *)
val 1 = square 1;
val 36 = square 6;


(* lab 1-6 *)
(* divisibleByThree: int -> bool 
   REQUIRES: true
   ENSURES: divisibleByThree n evaluates to true if n is a multiple of 3 and to false otherwise
*)
fun divisibleByThree (0 : int): bool = true
  | divisibleByThree 1 = false
  | divisibleByThree 2 = false
  | divisibleByThree x = divisibleByThree(x - 3); 
(* Testcase *)
val false = divisibleByThree 1;
val false = divisibleByThree 2;
val true = divisibleByThree 3;
val true = divisibleByThree 6;
val false = divisibleByThree 7;

(* lab 1-7 *)
(* oddP: int -> bool 
   REQUIRES: n >= 0
   ENSURES: evenP n evaluates to true iff n is odd
*)
fun oddP (0: int): bool = false
  | oddP 1 = true
  | oddP n = oddP (n - 2);
(* Testcase *)
val false = oddP 2;
val true = oddP 1;
val true = oddP 19;
val false = oddP 20;