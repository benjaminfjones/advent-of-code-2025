import AdventOfCode2025.Basic


def Intvl := Int × Int
def intvlContains (i: Intvl) (x: Int) : Bool := i.fst ≤ x && x ≤ i.snd
def parseIntvl : String → Intvl := fun s =>
  let ends := s.splitOn "-"
  (ends[0]!.toInt!, ends[1]!.toInt!)

def IntSet := List Intvl  -- a crude integer set
def intSetContains (is: IntSet) (x: Int) : Bool := is.any (fun intvl => intvlContains intvl x)
def intListMax (is: List Int) : Option Int :=
    aux none is
  where
    aux (curMax: Option Int) (is: List Int) := match is with
    | [] => curMax
    | hd :: tl => if curMax.isNone || hd > curMax.get! then
        aux hd tl
      else
        aux curMax tl
def intSetMax (is: IntSet) : Option Int := intListMax (is.map (fun iv => iv.snd))

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

-- repeated numbers whose period is < 10^n. e.g. if n = 3, then 123123 is in the list
def repeatedNums (n: Nat) : List Int :=
  let ds := range (10^n)
  let ds' := ds.filter (fun d => d >= 10^(n-1))
  ds'.map (fun d => d*(10^n+1))

#eval repeatedNums 2
#eval List.length (repeatedNums 5)  -- 100,000

/-- info: [] -/
#guard_msgs in
#eval let testSet := parseInputStr "1-10,50-100"
      (repeatedNums 2).filter (fun x => intSetContains testSet x)
/-- info: [55, 66, 77, 88, 99] -/
#guard_msgs in
#eval let testSet := parseInputStr "1-10,50-100"
      (repeatedNums 1).filter (fun x => intSetContains testSet x)


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
  pure $ List.sum ((List.range 6).flatMap (fun n => (repeatedNums n).filter (fun x => intSetContains p1_test x)))

/-- info: 52316131093 -/
#guard_msgs in
#eval do
  let p1_test ← parseInput "data/d2_p1"
  pure $ List.sum ((List.range 6).flatMap (fun n => (repeatedNums n).filter (fun x => intSetContains p1_test x)))

