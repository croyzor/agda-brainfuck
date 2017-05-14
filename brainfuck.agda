module brainfuck where

open import Data.Bool
open import Data.Char
open import Data.String using (String; toList)
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

data cmd : Set where

  -- Basic brainfuck commands, plus nop (no operation)
  nop add sub left right : cmd

  -- Loops will be handled by the parser, collecting the loop body into
  -- a list of commands
  loop : List cmd → cmd
  
  -- For sequencing multiple commands
  seq : cmd → cmd → cmd

-- Backwards version of List
data Bwd (X : Set) : Set where
  [] : Bwd X
  _<:_ : Bwd X → X → Bwd X

data Zipper (X : Set) : Set where
  _<[_]>_ : Bwd X → X → List X → Zipper X

Tape : Set
Tape = Zipper ℕ

-- Subract 1 (opposite of suc)
cus : ℕ → ℕ 
cus zero = 255
cus (suc n) = n

record Pair (X : Set) (Y : Set) : Set₁ where
  constructor _,_
  field
    fst : X
    snd : Y

_**_ : (X : Set) → (Y : Set) → Set₁
_**_ = Pair

range : ℕ → List ℕ
range zero = []
range (suc n) = range n ++ (suc n ∷ [])

-- Combine a list of commands into a sequence
seqlist : List cmd → cmd
seqlist [] = nop
seqlist (x ∷ xs) = seq x (seqlist xs)

-- Process one command
step : cmd → Tape → cmd ** Tape
step nop m = nop , m
step add (x <[ x₁ ]> x₂) = nop , (x <[ (suc x₁) ]> x₂)
step sub (x <[ x₁ ]> x₂) = nop , (x <[ (cus x₁) ]> x₂)

-- TODO: Make left and right loop at the edges of the tape
step left ([] <[ x₁ ]> x₂) = nop , ([] <[ x₁ ]> x₂)
step left ((x <: x₁) <[ x₂ ]> x₃) = nop , (x <[ x₁ ]> (x₂ ∷ x₃))

step right (x <[ x₁ ]> []) = nop , (x <[ x₁ ]> [])
step right (x <[ x₁ ]> (x₂ ∷ x₃)) = nop , ((x <: x₁) <[ x₂ ]> x₃)

-- If pointer is at zero, skip over the loop body
step (loop x) (x₁ <[ zero ]> x₃) = nop , (x₁ <[ zero ]> x₃)
step (loop x) (x₁ <[ suc x₂ ]> x₃) = seq (seqlist x) (loop x) , (x₁ <[ x₂ ]> x₃)

step (seq nop c) m = c , m
step (seq c c₁) m with step c m
step (seq c c₁) m | fst , snd = (seq fst c₁) , snd

-- 4 bit null memory
seed : Tape
seed = [] <[ 0 ]> (replicate 3 0)

-- Tokens for the parser (which does not yet handle loops)
data Token : Set where
  < > + - : Token

parseChar : Char → cmd
parseChar '>' = right
parseChar '<' = left
parseChar '+' = add
parseChar '-' = sub
parseChar c = nop

parse : String → List cmd
parse str = map parseChar (toList str)

testProgram : cmd
testProgram = seqlist (parse "->-->--->----")

-- Helper for stepping finitely
_steps : ℕ → cmd → Tape → Tape
_steps zero c m = m
_steps (suc n) nop m = m
_steps (suc n) (seq nop c₁) m = (suc n steps) c₁ m
_steps (suc n) c m with step c m
_steps (suc n) c m | cmds , tape = (n steps) cmds tape

test : (13 steps) testProgram seed ≡ ((([] <: 255) <: 254) <: 253) <[ 252 ]> []
test = refl

{-

This part fails the termination check (rightly so!)

runProgram : cmd → Tape → Tape
runProgram c m with step c m
runProgram c m | fst , snd = (runProgram fst snd)

test : Tape
test = runProgram testProgram seed

-}
