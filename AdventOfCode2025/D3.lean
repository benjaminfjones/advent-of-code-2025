import AdventOfCode2025.Basic

namespace D3

instance : Bind List where
  bind xs f := xs.flatMap f

instance : Pure List where
  pure a := [a]

instance : Monad List where
  bind := Bind.bind
  pure := Pure.pure

#guard (do
    let x ← [1,2,3]
    let y ← [10,11,12]
    pure (x,y))
  == [(1, 10), (1, 11), (1, 12), (2, 10), (2, 11), (2, 12), (3,10), (3,11), (3,12)]

def allButLast {α : Type} : List α → List α := fun xs =>
  let l := xs.length
  xs.take (l-1)
def allButFirst {α : Type} : List α → List α := fun xs =>
  xs.drop 1

#guard allButLast [1,2,3] == [1,2]
#guard allButFirst [1,2,3] == [2,3]
#guard List.zip (allButLast [1,2,3]) (allButFirst [1,2,3]) == [(1,2), (2,3)]

def pairDigitsToInt : Nat × Nat → Nat := fun (d1, d2) => 10*d1 + d2

#guard
  let xs := [1,2,3]
  List.max? (List.map pairDigitsToInt $ List.zip (allButLast xs) (allButFirst xs)) == some 23

-- Ordered pairs of distinct elements from the list, i.e. { (xs[i], xs[j]) | i < j }
def pairs {α : Type} : List α → List (α × α) := fun xs =>
    aux [] xs
  where
    aux (acc: List (α × α)) (xs: List α) := match xs with
    | [] => acc
    | _x :: [] => acc
    | x :: tl =>
      let xPairs := tl.map (fun t => (x,t))
      aux (acc ++ xPairs) tl

#guard pairs [1] == []
#guard pairs [1,2] == [(1,2)]
#guard pairs [1,2,3] == [(1,2), (1,3), (2,3)]

-- joltage is the max digit pairing in a battery bank
-- e.g. 1231234591238 --> 98
def joltage : List Nat → Nat := fun xs =>
  (List.max? (List.map pairDigitsToInt (pairs xs))).get!

#guard joltage [1,2,3,1,2,3,4,5,9,1,2,3,8] == 98


/------------------------------------------------------------------------
 Part 1

"The batteries are arranged into banks; each line of digits in your input
corresponds to a single bank of batteries. Within each bank, you need to turn
on exactly two batteries; the joltage that the bank produces is equal to the
number formed by the digits on the batteries you've turned on. For example, if
you have a bank like 12345 and you turn on batteries 2 and 4, the bank would
produce 24 jolts. (You cannot rearrange batteries.)

The total output joltage is the sum of the maximum joltage from each bank, so
in this example, the total output joltage is 98 + 89 + 78 + 92 = 357.

There are many batteries in front of you. Find the maximum joltage possible
from each bank; what is the total output joltage?"

 -----------------------------------------------------------------------/

def parseInput : System.FilePath → IO (List (List Nat)) := fun f => do
  let ls ← Array.toList <$> readLines f
  let digitChars := ls.map (fun s => s.toList)
  pure $ digitChars.map (fun ds => ds.map (fun c => c.toString.toNat!)

#eval parseInput "data/d3_test"

/-- info: 357 -/
#guard_msgs in
#eval do
  let input ← parseInput "data/d3_test"
  pure $ List.sum (input.map joltage)

/-- info: 17694 -/
#guard_msgs in
#eval do
  let input ← parseInput "data/d3"
  pure $ List.sum (input.map joltage)

/- ----------------------------------------------------------------------
 Part 2

"Now, you need to make the largest joltage by turning on exactly twelve
batteries within each bank."

 --------------------------------------------------------------------- -/

/-- remove `n` from the list, possibly many times, but do not go below a
    length of `m` -/
partial def removeNTillM (n m: Nat) (xs: List Nat) : List Nat :=
  if (xs.idxOf? n).isNone || xs.length <= m then
    xs
  else
    let xs' := xs.erase n
    -- TODO: prove that sizeOf xs' < sizeOf xs
    removeNTillM n m xs'

partial def fixpoint {α : Type} [BEq α] (f: α → α) (a: α) : α :=
  let a' := f a
  if a' == a then a else fixpoint f a'

#guard removeNTillM 1 5 [1,2,3,4,1,2] == [2,3,4,1,2]
#guard removeNTillM 2 5 [1,2,3,4,1,2] == [1,3,4,1,2]

#guard removeNTillM 1 6 [9,6,3,4,1,1,2] == [9,6,3,4,1,2]  -- removing the 1's results in larger number
#guard removeNTillM 2 5 [9,6,3,4,1,1,2] == [9,6,3,4,1,1]

#guard removeNTillM 1 12 [1,2,3,4,1] == [1,2,3,4,1]
#guard removeNTillM 1 12 [1,2,3,4,1,9,9,9,9,9,9,9,9] == [2,3,4,1,9,9,9,9,9,9,9,9]
#guard fixpoint (removeNTillM 1 3) [1,2,3,4,1] == [2,3,4]
#guard fixpoint (removeNTillM 1 12) [9,8,7,6,5,4,3,2,1,1,1,1,1,1,1] == [9,8,7,6,5,4,3,2,1,1,1,1]

#eval do
  let input ← parseInput "data/d3_test"
  let i := input[0]!
  let i := fixpoint (removeNTillM 1 12) i
  let i := fixpoint (removeNTillM 2 12) i
  let i := fixpoint (removeNTillM 3 12) i
  pure i
  /-
  let i' := input.map (fun i => fixpoint (removeNTillM 1 12) i)
  let i' := i'.map (fun i => fixpoint (removeNTillM 2 12) i)
  let i' := i'.map (fun i => fixpoint (removeNTillM 3 12) i)
  pure $ List.sum (i'.map joltage)
  -/

-- Reduce to the largest 12 digit sub-sequence
def reduce12 (xs: List Nat) : List Nat :=
  (List.range 10).foldl (fun ds n => fixpoint (removeNTillM n 12) ds) xs

#eval reduce12 [9,8,7,6,5,4,3,2,1,1,1,1,1,1,1]
#eval reduce12 [8,1,1,1,1,1,1,1,1,1,1,1,1,1,9]
#eval reduce12 [2,3,4,2,3,4,2,3,4,2,3,4,2,7,8]  -- this one is WRONG

/- Try removing each battery one at a time and pick the max
For example, [9,6,3,4,1,1,2]

634,112
934,112
964,112  <-- largest
963,112
963,412
963,412
963,411

Could be that removing the first element a[i] for which a[i] < a[i+1] is the
best move.

-/

def shrinkToLargest (xs: List Nat) : List Nat :=
  let abl := allButLast xs
  let pairs := List.zip abl (allButFirst xs)
  match pairs.findIdx? (fun (a,b) => a < b) with
  | none => abl
  | some n => xs.eraseIdx n

#guard shrinkToLargest [9,6,3,4,1,1,2] == [9,6,4,1,1,2]

-- Apply `shrinkToLargest` repeatedly until the list either stops changing or reaches
-- 12 elements or less
def shrinkToLargest12 (xs: List Nat) : List Nat :=
  let aux ys := if ys.length <= 12 then ys else shrinkToLargest ys
  fixpoint aux xs

#guard shrinkToLargest12 [9,6,3,4,1,1,2] == [9,6,3,4,1,1,2]
#guard shrinkToLargest12 [2,3,4,2,3,4,2,3,4,2,3,4,2,7,8]  == [4, 3, 4, 2, 3, 4, 2, 3, 4, 2, 7, 8]

-- take all the digits in the list and concatenate into a Nat
def bigJoltage : List Nat -> Nat := fun xs =>
  let n := xs.length
  let sumPow := xs.foldl (fun (sum, pow) x => (sum + x*10^pow, pow-1)) (0,n-1)
  sumPow.fst

#guard bigJoltage [] == 0
#guard bigJoltage [1] == 1
#guard bigJoltage [9,6,3,4,1,1,2] == 9634112

/-- Solution for part2 -/
def part2 : List (List Nat) → Nat := fun input =>
  let shrunkenBanks := input.map shrinkToLargest12
  List.sum (shrunkenBanks.map bigJoltage)

/-- info: 3121910778619 -/
#guard_msgs in
#eval do
  let input ← parseInput "data/d3_test"
  pure $ part2 input

/-- info: 175659236361660 -/
#guard_msgs in
#eval do
  let input ← parseInput "data/d3"
  pure $ part2 input

end D3
