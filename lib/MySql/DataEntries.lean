/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Pod.Float
import MySql.Utils

open Pod (Float32)

namespace MySql

-- NOTE: `extends` + default `by decide` + construct via {...} = inf loop?
structure Date where
  /-- [1000; 9999] -/
  year : UInt16
  year_ge_and_le : 1000 ≤ year.toNat ∧ year.toNat ≤ 9999 -- := by decide
  /-- [0;12) -/
  month : UInt8
  month_lt : month.toNat < 12 -- := by decide
  /-- [0;31) -/
  day : UInt8
  day_lt : day.toNat < 31 -- := by decide

instance : Inhabited Date := .mk {
  year := 1000
  month := 0
  day := 0
  year_ge_and_le := by decide
  month_lt := by decide
  day_lt := by decide
}

def Date.ofSubstring? (s : Substring) : Option Date := sorry

def Date.ofSubstring! : Substring → Date :=
  Option.get! ∘ Date.ofSubstring?

structure DateTime extends Date where
  hour : UInt8
  hour_lt : hour.toNat < 24 -- := by decide
  minute : UInt8
  minute_lt : minute.toNat < 60 -- := by decide
  second : UInt8
  second_lt : second.toNat < 60 -- := by decide

instance : Inhabited DateTime := .mk { (default : Date) with
  hour := 0
  minute := 0
  second := 0
  hour_lt := by decide
  minute_lt := by decide
  second_lt := by decide
}

def DateTime.ofSubstring? (s : Substring) : Option DateTime :=
  let space := s.posOf ' '
  Date.ofSubstring? ⟨s.str, s.startPos, s.startPos + space⟩ >>= λ date ↦
    let i : String.Pos := s.startPos + space + ⟨1⟩
    let h0 := s.str.get i
    let i := i + ⟨1⟩
    let h1 := s.str.get i
    let i := i + ⟨1⟩
    let hour := (h0.val - '0'.val) * 10 + (h1.val - '0'.val) |>.toUInt8
    if h: hour < 24 ∧ (h0.isDigit && h1.isDigit && s.str.get i == ':')
      then
        have hh : hour.toNat < 24 := sorry
        let i := i + ⟨1⟩
        let m0 := s.str.get i
        let i := i + ⟨1⟩
        let m1 := s.str.get i
        let i := i + ⟨1⟩
        let minute := (m0.val - '0'.val) * 10 + (m1.val - '0'.val) |>.toUInt8
        if h: minute < 60 ∧ (m0.isDigit && m1.isDigit && s.str.get i == ':')
          then
            have hm : minute.toNat < 60 := sorry
            let i := i + ⟨1⟩
            let s0 := s.str.get i
            let i := i + ⟨1⟩
            let s1 := s.str.get i
            let second := (s0.val - '0'.val) * 10 + (s1.val - '0'.val) |>.toUInt8
            if h: second < 60 ∧ (s0.isDigit && s1.isDigit)
              then
                have hs : second.toNat < 60 := sorry
                some { date with
                  hour, minute, second
                  hour_lt := hh
                  minute_lt := hm
                  second_lt := hs
                }
              else none
          else none
      else none

def DateTime.ofSubstring! : Substring → DateTime :=
  Option.get! ∘ DateTime.ofSubstring?

inductive DataEntry where
| null
| tinyint (x : UInt8)
| smallint (x : UInt16)
| mediumint (x : UInt32) (h : x.toNat < 2 ^ 24)
| int (x : UInt32)
| bigint (x : UInt64)
| float (f : Float32)
| double (f : Float)
| timestamp (t : UInt32)
| date (d : Date)
| datetime (d : DateTime)
| char (s : String)
| varchar (s : String)
| binary (b : ByteArray)
| varbinary (b : ByteArray)
| enum (s : String)
| set (ss : Array String)
| json (x : Lean.Json)
deriving Inhabited

instance {n} : OfNat DataEntry n where
  ofNat :=
    if h: n < 2 ^ 8 then
      .tinyint ⟨n, h⟩
    else if h: n < 2 ^ 16 then
      .smallint ⟨n, h⟩
    else if h: n < 2 ^ 24 then
      .mediumint ⟨n, Nat.lt_trans h (by decide)⟩ h
    else if h: n < 2 ^ 32 then
      .int ⟨n, h⟩
    else if h: n < 2 ^ 64 then
      .bigint ⟨n, h⟩
    else
      .varchar (toString n)

instance : Coe UInt8 DataEntry where
  coe := DataEntry.tinyint

instance : Coe UInt16 DataEntry where
  coe := DataEntry.smallint

instance : Coe UInt32 DataEntry where
  coe := DataEntry.int

instance : Coe UInt64 DataEntry where
  coe := DataEntry.bigint

instance : Coe Float32 DataEntry where
  coe := DataEntry.float

instance : Coe Float DataEntry where
  coe := DataEntry.double

instance : OfScientific DataEntry where
  ofScientific m s e := DataEntry.double (OfScientific.ofScientific m s e)

instance : Coe String DataEntry where
  coe := DataEntry.varchar

private
def appendHex (acc : String) (b : UInt8) : String :=
  let f (x : UInt8) : Char :=
    if h: x < 10 then
      .mk ('0'.val + x.toUInt32) $ by
        apply Or.inl
        show (48 + x.toNat % 2 ^ 32) % 2 ^ 32 < _
        have h1 : x.toNat < 2 ^ 32 := Nat.lt_trans x.1.2 (by decide)
        have h2 : 48 + x.toNat < 2 ^ 32 := by
          rewrite [Nat.add_comm]
          apply Nat.add_lt_of_lt_sub
          apply Nat.lt_trans x.1.2
          decide
        rewrite [
          Nat.mod_eq_of_lt h1,
          Nat.mod_eq_of_lt h2,
          Nat.add_comm
        ]
        apply Nat.add_lt_of_lt_sub
        apply Nat.lt_trans h
        decide
    else if h: x < 16 then
      .mk ('A'.val - 10 + x.toUInt32) $ by
        apply Or.inl
        show (55 + x.toNat % 2 ^ 32) % 2 ^ 32 < _
        have h2 : x.toNat < 2 ^ 32 := Nat.lt_trans x.1.2 (by decide)
        have h1 : 55 + x.toNat % 2 ^ 32 < 2 ^ 32 := by
          rewrite [Nat.mod_eq_of_lt h2, Nat.add_comm]
          apply Nat.add_lt_of_lt_sub
          apply Nat.lt_trans x.1.2
          decide
        rewrite [
          Nat.mod_eq_of_lt h1,
          Nat.mod_eq_of_lt h2,
          Nat.add_comm
        ]
        apply Nat.add_lt_of_lt_sub
        apply Nat.lt_trans h
        decide
    else
      '*'
  acc.push (f $ b >>> 4) |>.push (f $ b &&& 15)

def DateTime.ofTimestamp (t : UInt32) : DateTime := sorry

@[inline] private
def appendDec2 (num : UInt8) (s : String) : String :=
  cond (num < 10) (s.push '0') s ++ toString num

def Date.toString (date : Date) : String :=
  ToString.toString date.year
    |>.push '-'
    |> appendDec2 (date.month + 1)
    |>.push '-'
    |> appendDec2 (date.day + 1)

def DateTime.toString (dt : DateTime) : String :=
  dt.toDate.toString
    |>.push ' '
    |> appendDec2 dt.hour
    |>.push ':'
    |> appendDec2 dt.minute
    |>.push ':'
    |> appendDec2 dt.second

protected def DataEntry.toString : DataEntry → String
| null => "NULL"
| tinyint x => toString x
| smallint x => toString x
| mediumint x _ => toString x
| int x    => toString x
| bigint x    => toString x
| float x  => optimizeFloatString $ toString x
| double x  => optimizeFloatString $ toString x
| timestamp t => (DateTime.ofTimestamp t).toString
| date d => d.toString
| datetime d => d.toString
| char s => s!"'{s}'"
| varchar s => s!"'{s}'"
| binary b => cond b.isEmpty "''" $ b.foldl appendHex "0x"
| varbinary b => cond b.isEmpty "''" $ b.foldl appendHex "0x"
| enum s => s!"'{s}'"
| set ss => ss.foldl (λ acc s ↦ cond acc.isEmpty s $ acc.push ',' ++ s) "'" |>.push '\''
| json x => x.compress

instance : ToString DataEntry := ⟨DataEntry.toString⟩
