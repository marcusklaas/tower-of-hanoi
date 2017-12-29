module Main

-- GameState keeps track of the smallest peg in total, and then the smallest peg
-- on each tower from left to right
data GameState : Nat -> Nat -> Nat -> Nat -> Type where
     InitialLeft : (biggest : Nat) -> GameState biggest biggest Z Z
     InitialMid : (biggest : Nat) -> GameState biggest Z biggest Z
     InitialRight : (biggest : Nat) -> GameState biggest Z Z biggest
     NextLeft : (prevState : GameState (S k) _ b c) -> GameState k k b c
     NextMid : (prevState : GameState (S k) a _ c) -> GameState k a k c
     NextRight : (prevState : GameState (S k) a b _) -> GameState k a b k

data CompleteState : Nat -> Nat -> Nat -> Type where
     MkState : (GameState Z a b c) -> CompleteState a b c

main : IO ()
main = let
           state = MkState (NextRight $ NextLeft (InitialRight 2))
       in
           putStrLn "Hello, world!"
