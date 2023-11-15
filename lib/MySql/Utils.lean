/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Std

namespace MySql

/- Auxiliary functions to represent a `DataFrame` as a `String` -/

/- Removes trailing zeros form the right side of a string -/
def withoutRightmostZeros (s : Substring) : Substring :=
  s.dropRightWhile (· == '0')

/- Makes a string representation of a `Float` more compact -/
def optimizeFloatString (s : String) : String :=
  let split := s.splitOn "."
  let length := split.length
  if length = 1 then
    s
  else
    if length = 2 then
      let cleanR := withoutRightmostZeros split.getLast!
      split.head! ++ "." ++ (if cleanR.isEmpty then "0" else cleanR.toString)
    else
      panic! "ill-formed float string"

/- Fills the left side of a `String` with a character `c`, `n` times -/
def leftFillWithUntil (s : String) (c : Char) (n : Nat) : String := Id.run do
  let mut data : List Char := s.data
  for _ in [0 : n - s.length] do
    data := [c].append data
  ⟨data⟩

/- Parses a `Float` from a `String` -/
def toFloat! (s : String) : Float :=
  let split := s.splitOn "."
  let l := split.head!.splitOn "-"
  if split.length = 2 then
    let r := split.getLast!
    let rFloat := r.toNat!.toFloat / (10.0 ^ r.length.toFloat)
    if l.length = 1 then
      l.head!.toNat!.toFloat + rFloat
    else
      -1.0 * (l.getLast!.toNat!.toFloat + rFloat)
  else
    if l.length = 1 then
      l.head!.toNat!.toFloat
    else
      -1.0 * l.getLast!.toNat!.toFloat
