import Std
import AdventOfCode2025.Basic

def parseInputStr : String → IntSet := fun input => List.map parseIntvl $ input.splitOn ","

#guard intListMax [2,7,4,3,6,8,6,0,-1,10,3] == some 10
#guard intSetMax (parseInputStr "1-10,50-100") == some 100


/-- info: [(1, 10), (50, 100)] -/
#guard_msgs in
#eval parseInputStr "1-10,50-100"

#guard ¬ intSetContains (parseInputStr "1-10,50-100") 0
#guard intSetContains (parseInputStr "1-10,50-100") 5
#guard intSetContains (parseInputStr "1-10,50-100") 10
#guard ¬ intSetContains (parseInputStr "1-10,50-100") 20
#guard intSetContains (parseInputStr "1-10,50-100") 55
#guard ¬ intSetContains (parseInputStr "1-10,50-100") 105

def range (len: Nat) : List Int := List.map Int.ofNat (List.range len)

-- numbers repeated 2x whose period is < 10^n. e.g. if n = 3, then 123123 is in the list
def repeatedNums2 (n: Nat) : List Int :=
  let ds := range (10^n)
  let ds' := ds.filter (fun d => d >= 10^(n-1))  -- filter out numbers with leading zeros
  ds'.map (fun d => d*(10^n+1))

#eval repeatedNums2 2
#eval List.length (repeatedNums2 5)  -- 100,000

/-- info: [] -/
#guard_msgs in
#eval let testSet := parseInputStr "1-10,50-100"
      (repeatedNums2 2).filter (fun x => intSetContains testSet x)
/-- info: [55, 66, 77, 88, 99] -/
#guard_msgs in
#eval let testSet := parseInputStr "1-10,50-100"
      (repeatedNums2 1).filter (fun x => intSetContains testSet x)


/------------------------------------------------------------------------
 Part 1

 "Since the young Elf was just doing silly patterns, you can find the invalid
 IDs by looking for any ID which is made only of some sequence of digits
 repeated twice. So, 55 (5 twice), 6464 (64 twice), and 123123 (123 twice)
 would all be invalid IDs.

None of the numbers have leading zeroes; 0101 isn't an ID at all. (101 is a
valid ID that you would ignore.)
...

What do you get if you add up all of the invalid IDs?"

 -----------------------------------------------------------------------/

-- note: something weird about `readString` causes a panic during ellaboration and
-- an incorrect `0` as the last interval endpoint ??
def parseInput (filepath: String) : IO IntSet := do
  let ls ← readLines filepath
  pure (parseInputStr ls[0]!)


/-- info: 1227775554 -/
#guard_msgs in
#eval do
  let p1_test ← parseInput "data/d2_p1_test"
  pure $ List.sum ((List.range 6).flatMap (fun n => (repeatedNums2 n).filter (fun x => intSetContains p1_test x)))

/-- info: 52316131093 -/
#guard_msgs in
#eval do
  let p1_test ← parseInput "data/d2_p1"
  pure $ List.sum ((List.range 6).flatMap (fun n => (repeatedNums2 n).filter (fun x => intSetContains p1_test x)))



/------------------------------------------------------------------------
 Part 2

 "Now, an ID is invalid if it is made only of some sequence of digits repeated
 at least twice. So, 12341234 (1234 two times), 123123123 (123 three times),
 1212121212 (12 five times), and 1111111 (1 seven times) are all invalid IDs."

 -----------------------------------------------------------------------/

-- numbers repeated N times whose period is < 10^n. e.g. if N=3 and n = 2, then 646464 = 64*(10000 + 100 + 1) is in the list
def repeatedNumsN (N n: Nat) : List Int :=
  let ds := range (10^n)
  let ds' := ds.filter (fun d => d >= 10^(n-1))  -- filter out numbers with leading zeros
  let multiplier := List.sum (List.map (fun e => 10^(e*n)) (List.range N))
  ds'.map (fun d => d*multiplier)

/- #eval repeatedNumsN 3 2 -/
#guard (repeatedNumsN 3 2).length == 90
#eval (repeatedNumsN 10 1)
#guard (repeatedNums2 3).length == 900
-- there are overlaps
#guard
  let set := Std.HashSet.emptyWithCapacity 1000
  let set' := set.insertMany (repeatedNumsN 3 2)
  let set'' := set'.insertMany (repeatedNums2 3)
  let nums := set''.toList
  nums.length == 981

def overallRepeatedNums :=
  let set := Std.HashSet.emptyWithCapacity 1000
  -- numbers repeated twice w/ period < 10^n
  let set0 := set.insertMany  $ (List.range 6).flatMap (fun n => (repeatedNums2 n))
  -- numbers repeated twice w/ period < 10^n
  let set1 := set0
  /- let set1 := set0.insertMany $ (List.range 6).flatMap (fun n => (repeatedNumsN 2 n)) -/
  -- numbers repeated 3x w/ period < 10^n
  let set2 := set1.insertMany $ (List.range 5).flatMap (fun n => (repeatedNumsN 3 n))
  -- TODO: make it a fold
  let set3 := set2.insertMany $ (List.range 4).flatMap (fun n => (repeatedNumsN 4 n))
  let set4 := set3.insertMany $ (List.range 3).flatMap (fun n => (repeatedNumsN 5 n))
  let set5 := set4.insertMany $ (List.range 2).flatMap (fun n => (repeatedNumsN 6 n))
  let set6 := set5.insertMany $ (List.range 2).flatMap (fun n => (repeatedNumsN 7 n))
  let set7 := set6.insertMany $ (List.range 1).flatMap (fun n => (repeatedNumsN 8 n))
  let set8 := set7.insertMany $ (List.range 1).flatMap (fun n => (repeatedNumsN 9 n))
  let set9 := set8.insertMany $ (List.range 1).flatMap (fun n => (repeatedNumsN 10 n))
  set9.toList

#eval overallRepeatedNums.length

/-- info: 4174379265 -/
#guard_msgs in
#eval do
  let p2_test ← parseInput "data/d2_p1_test"
  pure $ List.sum (overallRepeatedNums.filter (fun x => intSetContains p2_test x))

/-- info: 69564213293 -/
#guard_msgs in
#eval do
  /- let startTime ← BaseIO.toIO IO.monoMsNow -/
  let p2 ← parseInput "data/d2_p1"
  let result := List.sum (overallRepeatedNums.filter (fun x => intSetContains p2 x))
  /- let endTime ← BaseIO.toIO IO.monoMsNow -/
  /- let duration := endTime - startTime -/
  /- IO.println s!"time: {duration}" -/
  pure $ result
