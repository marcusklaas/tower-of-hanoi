module Main

data GameState : Type where
     Initial : GameState
     LeftPeg : GameState -> GameState
     MidPeg : GameState -> GameState
     RightPeg : GameState -> GameState

-- do we even need the leftPrefixLength?
data LeftMidPrefix : (state : GameState) -> (leftPrefixLength : Nat) -> (suffix : GameState) -> Type where
     Here : LeftMidPrefix (MidPeg suffix) Z suffix
     There : (later : LeftMidPrefix seq k suffix) -> LeftMidPrefix (LeftPeg seq) (S k) suffix

data Move : Type where
     MidToRight : (prf : LeftMidPrefix st k suf) -> (st : GameState) -> Move

data UnprovenMove = LeftMid
                  | LeftRight
                  | MidLeft
                  | MidRight
                  | RightLeft
                  | RightMid

solve : GameState -> GameState
solve Initial = Initial
solve (LeftPeg x) = ?solve_rhs_2
solve (MidPeg x) = ?solve_rhs_3
solve (RightPeg x) = ?solve_rhs_4

main : IO ()
main = let
           state = LeftPeg $ LeftPeg $ RightPeg Initial
       in
           putStrLn "Hello, world!"
