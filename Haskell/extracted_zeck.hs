module Extracted_zeck where

import qualified Prelude

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

nth :: Prelude.Integer -> (([]) a1) -> a1 -> a1
nth n l default0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> case l of {
            ([]) -> default0;
            (:) x _ -> x})
    (\m -> case l of {
            ([]) -> default0;
            (:) _ t -> nth m t default0})
    n

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

fib :: Prelude.Integer -> Prelude.Integer
fib n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.succ 0)
      (\_ ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> Prelude.succ 0)
        (\n'' -> (Prelude.+) (fib n') (fib n''))
        n')
      n')
    n

zeck_lists :: Prelude.Integer -> ([]) (([]) Prelude.Integer)
zeck_lists n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (:) ([]) ([]))
    (\n1 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> (:) ([]) ((:) ((:) (Prelude.succ 0) ([])) ([])))
      (\n2 ->
      let {part1 = zeck_lists n1} in
      let {
       part2 = map (\xs -> (:)
                 (fib
                   ((Prelude.+) n2 (Prelude.succ (Prelude.succ (Prelude.succ
                     0))))) xs) (zeck_lists n2)}
      in
      app part1 part2)
      n1)
    n

find_fib_index_aux :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
                      -> Prelude.Integer
find_fib_index_aux n k b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> k)
    (\b' ->
    case (Prelude.<=) (fib (Prelude.succ k)) n of {
     Prelude.True -> find_fib_index_aux n (Prelude.succ k) b';
     Prelude.False -> k})
    b

min_level_for_index :: Prelude.Integer -> Prelude.Integer
min_level_for_index n =
  find_fib_index_aux n 0 (Prelude.succ n)

zeck :: Prelude.Integer -> ([]) Prelude.Integer
zeck n =
  let {m = min_level_for_index n} in
  let {all = zeck_lists (sub m (Prelude.succ 0))} in nth n all ([])

