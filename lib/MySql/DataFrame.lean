/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import MySql.DataEntries
import MySql.Utils

namespace MySql

inductive DataType
| tinyint
| smallint
| mediumint
| int
| bigint
| float
| double
| timestamp
| date
| datetime
| char
| varchar
| text
| enum
| set
| json
deriving Inhabited, Repr

/- Prouces a `DataEntry` given its `DataType` and a `String` -/
def DataType.entryOfString? (dataType : DataType) (s : String) : Except String DataEntry :=
  if s = "NULL" then .ok .null
  else match dataType with
  | .tinyint => s.toNat?.elim (.error s!"can't parse {s} as a Nat") (.ok ∘ .tinyint ∘ Nat.toUInt8)
  | .smallint => s.toNat?.elim (.error s!"can't parse {s} as a Nat") (.ok ∘ .smallint ∘ Nat.toUInt16)
  | .mediumint => do
    let n ← s.toNat?.elim (.error s!"can't parse {s} as a Nat") .ok
    if h: n < 2 ^ 24
      then
        .ok $ .mediumint n.toUInt32 $ by
          show n % 2 ^ 32 < 2 ^ 24
          rewrite [Nat.mod_eq_of_lt $ Nat.lt_trans h (by decide)]
          exact h
      else
        .error "mediumint ≥ 2^24"
  | .int => s.toNat?.elim (.error s!"can't parse {s} as a Nat") (.ok ∘ .int ∘ Nat.toUInt32)
  | .bigint => s.toNat?.elim (.error s!"can't parse {s} as a Nat") (.ok ∘ .bigint ∘ Nat.toUInt64)
  | .float => s.toFloat32?.elim (.error s!"can't parse {s} as a f32") (.ok ∘ .float)
  | .double => s.toFloat32?.elim (.error s!"can't parse {s} as a f64") (.ok ∘ .double ∘ Pod.Float32.toFloat)
  | .timestamp => (DateTime.ofSubstring? s).elim (.error s!"can't parse {s} as a datetime") (.ok ∘ .timestamp ∘ DateTime.toTimestamp)
  | .date => (DateTime.ofSubstring? s).elim (.error s!"can't parse {s} as a datetime") (.ok ∘ .date ∘ DateTime.toDate)
  | .datetime => (DateTime.ofSubstring? s).elim (.error s!"can't parse {s} as a datetime") (.ok ∘ .datetime)
  | .char => .ok $ .char s
  | .varchar => .ok $ .varchar s
  | .text => .ok $ .text s
  | .enum => .ok $ .enum s
  | .set => .ok $ .set (s.splitOn ",").toArray
  | .json => .json <$> Lean.Json.parse s

/- Prouces a `DataEntry` given its `DataType` and a `String` -/
def DataType.entryOfString! (dataType : DataType) (s : String) : DataEntry :=
  match dataType.entryOfString? s with
  | .error e => panic! e
  | .ok x => x

/- Whether a `DataEntry` is of a `DataType` or not -/
@[simp] def DataEntry.ofType : DataEntry → DataType → Bool
| .tinyint _, .tinyint => true
| .smallint _, .smallint => true
| .mediumint .., .mediumint => true
| .int _, .int => true
| .bigint _, .bigint => true
| .float _, .float => true
| .double _, .double => true
| .timestamp _, .timestamp => true
| .date _, .date => true
| .datetime _, .datetime => true
| .char _, .char => true
| .varchar _, .varchar => true
| .text _, .text => true
| .enum _, .enum => true
| .set _, .set => true
| .json _, .json => true
| .null, _ => true
| _, _ => false

instance : ToString DataType where
  toString
  | .tinyint => "tinyint"
  | .smallint => "smallint"
  | .mediumint => "mediumint"
  | .int => "int"
  | .bigint => "bigint"
  | .float => "float"
  | .double => "double"
  | .timestamp => "timestamp"
  | .date => "date"
  | .datetime => "datetime"
  | .char => "char"
  | .varchar => "varchar"
  | .text => "text"
  | .enum => "enum"
  | .set => "set"
  | .json => "json"

def DataEntry.type? : DataEntry → Option DataType
| .null => none
| .default => none
| .tinyint _ => some .tinyint
| .smallint _ => some .smallint
| .mediumint _ _ => some .mediumint
| .int _ => some .int
| .bigint _ => some .bigint
| .float _ => some .float
| .double _ => some .double
| .char _ => some .char
| .varchar _ => some .varchar
| .text _ => some .text
| .enum _ => some .enum
| .set _ => some .set
| .json _ => some .json
| .date _ => some .date
| .datetime _ => some .datetime
| .timestamp _ => some .timestamp

abbrev Header := List (DataType × String)

/- Returns the column types of a `Header` -/
def Header.colTypes (h : Header) : List DataType :=
  h.map fun x => x.1

/- Returns the column names of a `Header` -/
def Header.colNames (h : Header) : List String :=
  h.map fun x => x.2

abbrev DataEntries := List DataEntry

/- Given a list of `DataEntry` and a list of `DataType`, tells whether
  every `DataEntry` is of `DataType` in a "zip" logic -/
@[simp] def DataEntries.ofTypes : DataEntries → List DataType → Bool
  | e :: es, t :: ts => e.ofType t && ofTypes es ts
  | [],      []      => true
  | _,       _       => false

/-- Given a list of `DataType`, turns a list of `String` into a list of
  `DataEntry` according to the respective type from the list -/
def entriesOfStrings! : List DataType → List String → DataEntries
  | t :: ts, s :: ss => t.entryOfString! s :: (entriesOfStrings! ts ss)
  | _,       _       => []

/- Whether every list of `DataEntry` obeys to `DataEntries.ofTypes` -/
@[simp] def rowsOfTypes : List DataEntries → List DataType → Prop
  | row :: rows, types => row.ofTypes types ∧ rowsOfTypes rows types
  | [],          _     => True

/- Turns a list of `DataEntry` into a list of their respective `String`
  representation-/
def DataEntries.toStrings (r : DataEntries) : List String :=
  r.map DataEntry.toString

/- A DataFrame consists of:
  * A header, containing the column names and their types
  * The rows, containing the actual data
  * A consistenty rule, guaranteeing that every row obeys to the scheme -/
structure DataFrame where
  header     : Header
  rows       : List DataEntries
  consistent : rowsOfTypes rows header.colTypes := by simp

namespace DataFrame

/- The column types of a `DataFrame` -/
def colTypes (df : DataFrame) : List DataType :=
  df.header.colTypes

/- The column names of a `DataFrame` -/
def colNames (df : DataFrame) : List String :=
  df.header.colNames

/- Returns an empty `DataFrame` -/
def empty (header : Header := []) : DataFrame :=
  ⟨header, [], by simp⟩

/- Given a `DataFrame` `df` and a new `Row` `r` that's consistent with its
  scheme, the concatenation of the `df.rows` and `r` is also consistent
  with the scheme of `df` -/
theorem consistentConcatOfConsistentRow
    {df : DataFrame} (row : DataEntries)
    (_hc : row.ofTypes df.colTypes) :
      rowsOfTypes (df.rows.concat row) (Header.colTypes df.header) :=
  match df with
    | ⟨_, rows, hr⟩ => by
      induction rows with
        | cons _ _ hi => exact ⟨hr.1, hi hr.2 _hc⟩
        | nil         =>
          simp only [colTypes] at _hc
          simp only [rowsOfTypes, _hc, and_self]

/- Adds a new row on a `DataFrame` -/
def addRow (df : DataFrame) (row : DataEntries)
    (h : row.ofTypes df.colTypes := by simp) : DataFrame :=
  ⟨df.header, df.rows.concat row, consistentConcatOfConsistentRow row h⟩

/- The number of rows in a `DataFrame` -/
def nRows (df : DataFrame) : Nat :=
  df.rows.length

/- The number of columns in a `DataFrame` -/
def nCols (df : DataFrame) : Nat :=
  df.header.length

/- The shape of a `DataFrame` (# of rows × # of columns) -/
def shape (df : DataFrame) : Nat × Nat :=
  (df.nRows, df.nCols)

/- The i-th row of a `DataFrame` -/
def row! (df : DataFrame) (i : Nat) : DataEntries :=
  if i >= df.rows.length then
    panic! s!"invalid index {i}"
  else
    (df.rows.get! i)

/- The i-th's rows of a `DataFrame` -/
def rows! (df : DataFrame) (li : List Nat) : List DataEntries := Id.run do
  let mut invalidIndexes : List Nat := []
  for i in li do
    if i >= df.rows.length then
      invalidIndexes := invalidIndexes.concat i
  if ¬invalidIndexes.isEmpty then
    panic! s!"invalid indexes {invalidIndexes}"
  else
    li.map fun i => df.row! i

/- The j-th column of a `DataFrame` -/
def col! (df : DataFrame) (j : Nat) : DataEntries :=
  if j >= df.header.length then
    panic! s!"invalid index {j}"
  else
    df.rows.map fun r => r.get! j

/- The j-th's columns of a `DataFrame` -/
def cols! (df : DataFrame) (lj : List Nat) : List DataEntries := Id.run do
  let mut invalidIndexes : List Nat := []
  for j in lj do
    if j >= df.header.length then
      invalidIndexes := invalidIndexes.concat j
  if ¬invalidIndexes.isEmpty then
    panic! s!"invalid indexes {invalidIndexes}"
  else
    lj.map fun j => df.col! j

/- The element at the i-th row and j-th column -/
def at! (df : DataFrame) (i j : Nat) : DataEntry :=
  if i >= df.rows.length then
    panic! s!"invalid row index {i}"
  else
    if j >= df.header.length then
      panic! s!"invalid column index {j}"
    else
      (df.row! i).get! j

/- The `String` representation of a `DataFrame` -/
def toString (df : DataFrame) : String := Id.run do
  if df.nCols = 0 then ""
  else
    let mut cells : List (List String) := []
    let mut colLengths : List Nat := []
    let mut header : List String := []
    for colName in df.colNames do
      colLengths := colLengths.concat colName.length
      header := header.concat colName
    cells := cells.concat header
    for row in df.rows do
      let mut line : List String := []
      let rowStrings : List String := row.toStrings
      for j in [0 : rowStrings.length] do
        let s := rowStrings.get! j
        let s_length : Nat := s.length
        if s_length > (colLengths.get! j) then
          colLengths := colLengths.set j s_length
        line := line.concat s
      cells := cells.concat line
    let mut res : String := ""
    for i in [0 : cells.length] do
      let row := cells.get! i
      for j in [0 : row.length] do
        let val : String := row.get! j
        res := res ++ "|" ++
          (leftFillWithUntil val ' ' (colLengths.get! j))
      res := res ++ "|"
      if cells.length = 1 ∨ i < cells.length - 1 then
        res := res ++ "\n"
      if i = 0 then
        for j in [0 : row.length] do
          res := res ++ "|" ++
            leftFillWithUntil "" '-' (colLengths.get! j)
        res := res ++ "|\n"
    res

instance : ToString DataFrame where
  toString df := df.toString

end DataFrame
