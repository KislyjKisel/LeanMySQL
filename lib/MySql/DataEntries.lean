/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Pod.Float
import Pod.Int
import MySql.Utils

open Pod (Float32 Int32 Int64)

namespace MySql

structure Date where
  /-- [1000; 9999] -/
  year : UInt16
  year_ge_and_le : 1000 ≤ year.toNat ∧ year.toNat ≤ 9999
  /-- [0;12) -/
  month : UInt8
  month_lt : month.toNat < 12
  /-- [0;31) -/
  day : UInt8
  day_lt : day.toNat < 31

instance : Inhabited Date := .mk {
  year := 1000
  month := 0
  day := 0
  year_ge_and_le := by decide
  month_lt := by decide
  day_lt := by decide
}

def Date.ofSubstring? (s : Substring) : Option Date :=
  let i : String.Pos := s.startPos
  let y0 := s.str.get i
  let i := i + ⟨1⟩
  let y1 := s.str.get i
  let i := i + ⟨1⟩
  let y2 := s.str.get i
  let i := i + ⟨1⟩
  let y3 := s.str.get i
  let i := i + ⟨1⟩
  let year := (y0.val - '0'.val) * 1000 + (y1.val - '0'.val) * 100 +
    (y2.val - '0'.val) * 10 + (y3.val - '0'.val) |>.toUInt16
  if h: (1000 ≤ year ∧ year ≤ 9999) ∧
    (y0.isDigit && y1.isDigit && y2.isDigit && y3.isDigit && s.str.get i == '-')
    then
      have hy : 1000 ≤ year.toNat ∧ year.toNat ≤ 9999 := by
        rewrite [UInt16.toNat]
        exact h.1
      let i := i + ⟨1⟩
      let m0 := s.str.get i
      let i := i + ⟨1⟩
      let m1 := s.str.get i
      let i := i + ⟨1⟩
      let month := (m0.val - '0'.val) * 10 + (m1.val - '0'.val) |>.toUInt8
      let month := month - 1
      if h: month < 12 ∧ (m0.isDigit && m1.isDigit && s.str.get i == '-')
        then
          have hm : month.toNat < 12 := by
            rewrite [UInt8.toNat]
            exact h.1
          let i := i + ⟨1⟩
          let d0 := s.str.get i
          let i := i + ⟨1⟩
          let d1 := s.str.get i
          let i := i + ⟨1⟩
          let day := (d0.val - '0'.val) * 10 + (d1.val - '0'.val) |>.toUInt8
          let day := day - 1
          if h: day < 31 ∧ (d0.isDigit && d1.isDigit && i == s.stopPos)
            then
              have hd : day.toNat < 31 := by
                rewrite [UInt8.toNat]
                exact h.1
              some {
                year, month, day
                year_ge_and_le := hy
                month_lt := hm
                day_lt := hd
              }
            else
              none
        else
          none
    else
      none

def Date.ofSubstring! : Substring → Date :=
  Option.get! ∘ Date.ofSubstring?

structure DateTime extends Date where
  hour : UInt8
  hour_lt : hour.toNat < 24
  minute : UInt8
  minute_lt : minute.toNat < 60
  second : UInt8
  second_lt : second.toNat < 60

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
        have hh : hour.toNat < 24 := by
          rewrite [UInt8.toNat]
          exact h.1
        let i := i + ⟨1⟩
        let m0 := s.str.get i
        let i := i + ⟨1⟩
        let m1 := s.str.get i
        let i := i + ⟨1⟩
        let minute := (m0.val - '0'.val) * 10 + (m1.val - '0'.val) |>.toUInt8
        if h: minute < 60 ∧ (m0.isDigit && m1.isDigit && s.str.get i == ':')
          then
            have hm : minute.toNat < 60 := by
              rewrite [UInt8.toNat]
              exact h.1
            let i := i + ⟨1⟩
            let s0 := s.str.get i
            let i := i + ⟨1⟩
            let s1 := s.str.get i
            let i := i + ⟨1⟩
            let second := (s0.val - '0'.val) * 10 + (s1.val - '0'.val) |>.toUInt8
            if h: second < 60 ∧ (s0.isDigit && s1.isDigit && i == s.stopPos)
              then
                have hs : second.toNat < 60 := by
                  rewrite [UInt8.toNat]
                  exact h.1
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

def DateTime.first : DateTime := .ofSubstring! "1000-01-01 00:00:00"
def DateTime.last : DateTime := .ofSubstring! "9999-12-31 23:59:59"

inductive DataEntry where
| null
| default
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
| text (s : String)
| binary (b : ByteArray)
| varbinary (b : ByteArray)
| blob (b : ByteArray)
| enum (s : String)
| set (ss : Array String)
| json (x : Lean.Json)
deriving Inhabited

instance {n} : OfNat DataEntry n where
  ofNat :=
    if h: n < UInt8.size then
      .tinyint ⟨n, h⟩
    else if h: n < UInt16.size then
      .smallint ⟨n, h⟩
    else if h: n < 2 ^ 24 then
      .mediumint ⟨n, Nat.lt_trans h (by decide)⟩ h
    else if h: n < UInt32.size then
      .int ⟨n, h⟩
    else if h: n < UInt64.size then
      .bigint ⟨n, h⟩
    else
      .varchar (toString n)

instance : Coe Bool DataEntry where
  coe := DataEntry.tinyint ∘ UInt8.ofBool

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

def DateTime.ofTimestamp (t : UInt32) : DateTime :=
  let z := t / 86400 + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let year := yoe + era * 400 |>.toUInt16
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let day := doy - (153 * mp + 2) / 5 |>.toUInt8
  let month := (if mp < 10 then mp + 2 else mp - 10) |>.toUInt8
  let year := year + UInt16.ofBool (month ≤ 2)
  let second := (t % 60).toUInt8
  have second_lt : second.toNat < 60 := by
    rewrite [UInt8.toNat]
    show (t.toNat % 60) % UInt8.size < 60
    have h1 : t.toNat % 60 < 60 := Nat.mod_lt t.toNat (by decide)
    have : t.toNat % 60 < UInt8.size := Nat.lt_trans h1 (by decide)
    rewrite [Nat.mod_eq_of_lt this]
    exact h1
  let minute := (t / 60) % 60 |>.toUInt8
  have minute_lt : minute.toNat < 60 := by
    rewrite [UInt8.toNat]
    show ((t / 60).toNat % 60) % UInt8.size < 60
    have h1 : (t / 60).toNat % 60 < 60 := Nat.mod_lt _ (by decide)
    have : (t / 60).toNat % 60 < UInt8.size := Nat.lt_trans h1 (by decide)
    rewrite [Nat.mod_eq_of_lt this]
    exact h1
  let hour := (t / 3600) % 24 |>.toUInt8
  have hour_lt : hour.toNat < 24 := by
    rewrite [UInt8.toNat]
    show ((t / 3600).toNat % 24) % UInt8.size < 24
    have h1 : (t / 3600).toNat % 24 < 24 := Nat.mod_lt _ (by decide)
    have : (t / 3600).toNat % 24 < UInt8.size := Nat.lt_trans h1 (by decide)
    rewrite [Nat.mod_eq_of_lt this]
    exact h1
  if h: 1000 ≤ year ∧ year ≤ 9999 ∧ month < 12 ∧ day < 31 -- m/d provable
    then
      {
        year, month, day, hour, minute, second
        year_ge_and_le := by rewrite [UInt16.toNat]; exact ⟨h.1, h.2.1⟩
        month_lt := by rewrite [UInt8.toNat]; exact h.2.2.1
        day_lt := by rewrite [UInt8.toNat]; exact h.2.2.2
        hour_lt, minute_lt, second_lt
      }
    else
      cond (year < 1000) DateTime.first DateTime.last

def DateTime.toTimestamp (dt : DateTime) : UInt32 :=
  let year := dt.year.toUInt32 - UInt32.ofBool (dt.month < 2)
  let era := year / 400
  let yoe := year - era * 400
  let doy := (153 * (cond (dt.month > 1) (dt.month - 2) (dt.month + 10)).toUInt32 + 2) / 5 + dt.day.toUInt32;
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  let days := Int64.ofUInt32 (era * 146097 + doe) - 719468
  Int32.val $
    Int32.ofUInt8 dt.second +
    Int32.ofUInt8 dt.minute * 60 +
    Int32.ofUInt8 dt.hour * 3600 +
    days.toInt32 * 86400

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
| default => "DEFAULT"
| tinyint x => toString x
| smallint x => toString x
| mediumint x _ => toString x
| int x => toString x
| bigint x => toString x
| float x => optimizeFloatString $ toString x
| double x => optimizeFloatString $ toString x
| timestamp t => s!"'{(DateTime.ofTimestamp t).toString}'"
| date d => s!"'{d.toString}'"
| datetime d => s!"'{d.toString}'"
| char s => s!"'{s}'"
| varchar s => s!"'{s}'"
| text s => s!"'{s}'"
| binary b => cond b.isEmpty "''" $ b.foldl appendHex "0x"
| varbinary b => cond b.isEmpty "''" $ b.foldl appendHex "0x"
| blob b => cond b.isEmpty "''" $ b.foldl appendHex "0x"
| enum s => s!"'{s}'"
| set ss => ss.foldl (λ acc s ↦ cond acc.isEmpty s $ acc.push ',' ++ s) "'" |>.push '\''
| json x => x.compress

instance : ToString DataEntry := ⟨DataEntry.toString⟩
