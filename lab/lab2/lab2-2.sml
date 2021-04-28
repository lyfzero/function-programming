fun all (your, base) = 
    case your of
        0 => base
      | _ => "are belong to us"::all(your - 1, base);

fun funny (f, []) = 0
  | funny (f, x::xs) = f(x, funny(f, xs));


(fn x => (fn y => x)) "Hello, world!";