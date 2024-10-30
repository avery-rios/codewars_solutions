module Postfix where

begin :: (() -> r) -> r
begin f = f ()

push :: e -> Int -> ((Int, e) -> r) -> r
push e v f = f (v, e)

add :: (Int, (Int, e)) -> ((Int, e) -> r) -> r
add (l, (r, e)) f = f (l + r, e)

end :: (Int, e) -> Int
end (v, _) = v
