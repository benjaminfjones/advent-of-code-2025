def hello := "world"

def readLines : System.FilePath → IO (Array String) := IO.FS.lines
def readString : System.FilePath → IO String := IO.FS.readFile
def readInts (f : System.FilePath) : IO (Array Int) := do
  let ls ← IO.FS.lines f
  pure (Array.map String.toInt! ls)


/-
Section on integer lists, sets, and intervals
-/

-- Integer interval
def Intvl := Int × Int

def intvlContains (i: Intvl) (x: Int) : Bool := i.fst ≤ x && x ≤ i.snd

/-- "n-m" --> (n, m) -/
def parseIntvl : String → Intvl := fun s =>
  let ends := s.splitOn "-"
  (ends[0]!.toInt!, ends[1]!.toInt!)

/-- A crude integer set based on intervals -/
def IntSet := List Intvl
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

/-
Section on `String`s, `Substring`s, and string `Iterators`
-/
open String
open Iterator

#guard "".isPrefixOf "goo"
#guard hasNext (mkIterator "foo") == true
#guard (next (mkIterator "foo")).remainingToString == "oo"
#guard (next (mkIterator "b")).remainingToString == ""
#guard (next (mkIterator "")).remainingToString == ""

-- decide if 2nd arg is a substring of 1st
partial def isSubstring : String → String → Bool
  | _, "" => true
  | "", _ => false
  | s, target =>
    if target.isPrefixOf s then
      true
    else
      let i := mkIterator s
      let i' := i.next
      let s' := i'.remainingToString
      -- have : ¬ i.atEnd = true := by sorry
      -- have h : sizeOf s' < sizeOf s := by
      --   sorry
      --   -- apply Iterator.sizeOf_next_lt_of_atEnd i this
      isSubstring s' target
  -- termination_by s t => sizeOf s


#check Iterator.sizeOf_next_lt_of_atEnd
#guard isSubstring "foobar" "foo"
#guard isSubstring "foobar" "bar"
#guard isSubstring "foobar" "oob"
#guard isSubstring "foobar" "quux" == false

-- Version of `isSubstring` using `Iterator` where the termination
-- argument goes through automagically!
def isSubstring' (s sub : String) : Bool :=
    match s, sub with
      -- handle the special case, otherwise go returns false for "" ""
      | "", "" => true
      | s', _ => go (mkIterator s')
  where
    go i :=
      if i.atEnd then
        false
      else
        let s' := i.remainingToString
        if sub.isPrefixOf s' then
          true
        else
          go i.next

#guard isSubstring' "foobar" "foo"
#guard isSubstring' "foobar" "bar"
#guard isSubstring' "foobar" "oob"
#guard isSubstring' "foobar" "quux" == false
#guard isSubstring' "foobar" ""
#guard isSubstring' "" ""


/-
List utilities
-/

def windows {α: Type} [BEq α] (n: Nat) (xs: List α) : List (List α) :=
  if xs.length < n || n == 0 then
    []
  else
    let w0 := xs.take n
    match xs with
      | [] => []
      | _ :: tl =>
        w0 :: windows n tl

#guard windows 0 [1, 2, 3, 4] == []
#guard windows 2 ([]: List Nat) == []
#guard windows 1 [1, 2, 3, 4] == [[1], [2], [3], [4]]
#guard windows 2 [1, 2, 3, 4] == [[1,2], [2,3], [3,4]]
