fun map f[] = []
  | map f(x::xs) = (f x) :: (map f xs);

fun filter f[] = []
  | filter f(x::xs) = if f x then x :: (filter f xs) else filter f xs;

map (filter (fn a=> size a = 4)) [["Sunday", "Monday"],["one", "two", "three", "four", "five"], ["year", "month", "day"]];
