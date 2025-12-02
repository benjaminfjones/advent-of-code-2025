import AdventOfCode2025.Basic

def maxDial : Int := 100
def initDial : Int := 50

def insToRotation : String → Int := fun ins =>
  let num := ins.mkIterator.next.remainingToString.toInt!
  if "R".isPrefixOf ins then
    num
  else
    -num

#guard insToRotation "L10" == -10
#guard insToRotation "L120" == -120
#guard insToRotation "L0" == 0
#guard insToRotation "R0" == 0
#guard insToRotation "R1" == 1
#guard insToRotation "R150" == 150

#check List.foldl

def foldDoRot : Int × Nat → Int → Int × Nat := fun (cur, sum) rot =>
  let cur' := (cur + rot) % maxDial
  (cur', if cur' == 0 then sum + 1 else sum)

def foldExpandRot : Int × List Int → Int → Int × List Int:= fun (cur, acc) rot =>
  let cur' := (cur + rot) % maxDial
  (cur', cur' :: acc)

/------------------------------------------------------------------------
 Part 1

 "The attached document (your puzzle input) contains a sequence of rotations,
 one per line, which tell you how to open the safe. A rotation starts with an L
 or R which indicates whether the rotation should be to the left (toward lower
 numbers) or to the right (toward higher numbers). Then, the rotation has a
 distance value which indicates how many clicks the dial should be rotated in
 that direction.

The dial starts by pointing at 50.

You could follow the instructions, but your recent required official North Pole
secret entrance security training seminar taught you that the safe is actually
a decoy. The actual password is the number of times the dial is left pointing
at 0 after any rotation in the sequence."

 -----------------------------------------------------------------------/
 
def parseInput (filepath: String) : IO (Array Int) := (Array.map insToRotation) <$> readLines filepath
def p1_test := parseInput "data/d1_p1_test"

#eval p1_test

#eval do
  let ins ← p1_test
  pure $ List.foldl foldExpandRot (initDial, []) ins.toList

/-- info: ['c', 'b', 'a'] -/
#guard_msgs in
#eval List.reverse "abc".toList

/- Part 1 test -/

/-- info: (32, 3) -/
#guard_msgs in
#eval (do
  let ins ← p1_test
  pure $ List.foldl foldDoRot (initDial, 0) ins.toList)

def p1_input := parseInput "data/d1_p1"

/-- info: (37, 1132) -/
#guard_msgs in
#eval (do
  let ins ← p1_input
  pure $ List.foldl foldDoRot (initDial, 0) ins.toList)

/------------------------------------------------------------------------
 Part 2

 "You remember from the training seminar that "method 0x434C49434B" means
 you're actually supposed to count the number of times any click causes the
 dial to point at 0, regardless of whether it happens during a rotation or at
 the end of one."

 -----------------------------------------------------------------------/

-- aux:
-- (50, 0) R51 c <- 0
-- (51, 0) R50
-- (52, 0) R49
-- ...
-- (0, 1)  R01 c <- c+1
-- (1, 1)  R00
def foldDoRot2 : Int × Nat → Int → Int × Nat := fun (cur, sum) rot =>
    let (final, stopsAtZero) := if rot >= 0 then
                                  aux (cur, 0) 1 (Int.natAbs rot)
                                else
                                  aux (cur, 0) (-1) (Int.natAbs rot)
    (final, stopsAtZero + sum)
  where
    -- aux is structured as recursive over r, the (Nat) absolute value of rotation
    -- so that the termination argument goes through automatically
    aux : Int × Nat → Int → Nat → Int × Nat := fun (t, c) sign r => match r with
    | 0 => (t, c)
    | s+1 => let t' := (t+sign) % maxDial
           aux (t', if t' == 0 then c+1 else c) sign s

/-- info: (1, 1) -/
#guard_msgs in
#eval foldDoRot2 (50, 0) 51

/-- info: (32, 6) -/
#guard_msgs in
#eval (do
  let ins ← p1_test
  pure $ List.foldl foldDoRot2 (initDial, 0) ins.toList)

/-- info: (37, 6623) -/
#guard_msgs in
#eval (do
  let ins ← p1_input
  pure $ List.foldl foldDoRot2 (initDial, 0) ins.toList)

