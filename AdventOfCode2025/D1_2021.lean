import AdventOfCode2025.Basic
-- import Init.Data.String.Basic
/-
As the submarine drops below the surface of the ocean, it automatically performs a sonar sweep of the nearby sea floor. On a small screen, the sonar sweep report (your puzzle input) appears: each line is a measurement of the sea floor depth as the sweep looks further and further away from the submarine.

For example, suppose you had the following report:

199
200
208
210
200
207
240
269
260
263

This report indicates that, scanning outward from the submarine, the sonar sweep found depths of 199, 200, 208, 210, and so on.

The first order of business is to figure out how quickly the depth increases, just so you know what you're dealing with - you never know if the keys will get carried into deeper water by an ocean current or a fish or something.

To do this, count the number of times a depth measurement increases from the previous measurement. (There is no measurement before the first measurement.) In the example above, the changes are as follows:

199 (N/A - no previous measurement)
200 (increased)
208 (increased)
210 (increased)
200 (decreased)
207 (increased)
240 (increased)
269 (increased)
260 (decreased)
263 (increased)
In this example, there are 7 measurements that are larger than the previous measurement.

How many measurements are larger than the previous measurement?

-/

-- read lines from a text file
-- see https://github.com/leanprover/lean4/blob/master/src/Init/System/IO.lean
-- https://github.com/leanprover/lean4/blob/master/src/Init/System/IO.lean#L1024

def d1_2021_p1 : IO Nat := do
  let ls <- readInts (System.FilePath.mk "data/test_d1_2021")
  let preds := Array.take ls ls.size.pred
  let succs := Array.drop ls 1
  let pairs := Array.zip preds succs
  let incs := Array.filter (fun (d1, d2) => d2 - d1 > (0 : Int)) pairs
  pure incs.size

/-
Day 1 part 2

In rust...

pub fn d1_part2(input_file: &str) -> usize {
    let es = util::read_ints(input_file).unwrap();
    let windows: Vec<&[i64]> = es.windows(3).collect();
    let len = windows.len();
    let preds = &windows[0..len];
    let succs = &windows[1..];
    preds
        .iter()
        .zip(succs)
        .filter(|(&pw, &sw)| sw[2] > pw[0])
        .count()
}

-/
